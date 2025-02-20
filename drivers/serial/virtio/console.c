/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * This driver follows the non-legacy virtIO 1.2 specification for the console device.
 * It assumes that the transport method is MMIO.
 * This driver is very minimal and was written for the goal of building systems that
 * use virtIO block devices in a simulator like QEMU. It is *not* written with
 * performance in mind. It makes use of no console device features and hence only has
 * a single set of receive/transmit virtqs and does not use control queues.
 *
 * It should also be noted that because this driver is intended to be used with a
 * simulator such as QEMU, things like memory fences when touching device registers
 * may be needed if instead this driver was to be used in a different environment.
 */

#include <microkit.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include <sddf/resources/device.h>
#include <sddf/serial/config.h>
#include "console.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

/*
 * The 'hardware' ring buffer region is used to store the virtIO virtqs
 */
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

/* The number of entries in each virtqueue */
#define RX_COUNT 512
#define TX_COUNT 512

/*
 * This default is based on the default QEMU setup but could change
 * depending on the instantiation of QEMU or wherever this driver is
 * being used.
 */
#ifndef VIRTIO_MMIO_CONSOLE_OFFSET
#define VIRTIO_MMIO_CONSOLE_OFFSET (0xe00)
#endif

#define VIRTIO_SERIAL_RX_QUEUE 0
#define VIRTIO_SERIAL_TX_QUEUE 1

/* Queues for communicating with the virtualizers */
serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

serial_queue_t *rx_queue;
serial_queue_t *tx_queue;

char *rx_data;
char *tx_data;

/* Used for storing characters to/from VirtIO */
char *virtio_rx_char;
char *virtio_tx_char;

struct virtq rx_virtq;
struct virtq tx_virtq;
uint16_t rx_last_seen_used = 0;
uint16_t tx_last_seen_used = 0;

uintptr_t virtio_rx_char_paddr;
uintptr_t virtio_tx_char_paddr;

/* Allocator for Rx descriptors */
ialloc_t rx_ialloc_desc;
uint32_t rx_descriptors[RX_COUNT];

/* Allocator for storing Tx characters */
ialloc_t tx_char_ialloc_desc;
uint32_t tx_char_desc[TX_COUNT];

/* Allocator for Tx descriptors */
ialloc_t tx_ialloc_desc;
uint32_t tx_descriptors[TX_COUNT];

/* Allocator for storing Rx characters */
ialloc_t rx_char_ialloc_desc;
uint32_t rx_char_desc[RX_COUNT];

int rx_last_desc_idx = 0;
int tx_last_desc_idx = 0;

static inline bool virtio_avail_full_rx(struct virtq *virtq)
{
    return rx_last_desc_idx >= rx_virtq.num;
}

static inline bool virtio_avail_full_tx(struct virtq *virtq)
{
    return tx_last_desc_idx >= tx_virtq.num;
}

/* The virtio MMIO region */
uintptr_t uart_base;
volatile virtio_mmio_regs_t *uart_regs;

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!virtio_avail_full_tx(&tx_virtq) && !serial_dequeue(&tx_queue_handle, &c)) {

        /* First, allocate somewhere to put the character */
        uint32_t char_idx = -1;
        int err = ialloc_alloc(&tx_char_ialloc_desc, &char_idx);
        assert(!err && char_idx != -1);

        /* Now we need to a descriptor to put into the virtIO ring */
        uint32_t pkt_desc_idx = -1;
        err = ialloc_alloc(&tx_ialloc_desc, &pkt_desc_idx);
        assert(!err && pkt_desc_idx != -1);

        /* We should not run out of descriptors assuming that the avail ring is not full. */
        assert(pkt_desc_idx < tx_virtq.num);

        /* Put the character into the data region */
        virtio_tx_char[char_idx] = c;

        /* Set up the packet */
        tx_virtq.desc[pkt_desc_idx].addr = virtio_tx_char_paddr + char_idx;
        tx_virtq.desc[pkt_desc_idx].len = 1;
        tx_virtq.desc[pkt_desc_idx].flags = 0;

        /* Enqueue the packet */
        tx_virtq.avail->ring[tx_virtq.avail->idx % tx_virtq.num] = pkt_desc_idx;

        tx_virtq.avail->idx++;
        tx_last_desc_idx += 1;

        transferred = true;
    }

    if (transferred) {
        /* Finally, need to notify the queue if we have transferred data */
        /* This assumes VIRTIO_F_NOTIFICATION_DATA has not been negotiated */
        uart_regs->QueueNotify = VIRTIO_SERIAL_TX_QUEUE;
        if (serial_require_consumer_signal(&tx_queue_handle)) {
            serial_cancel_consumer_signal(&tx_queue_handle);
            microkit_notify(config.tx.id);
        }
    }
}

static void tx_return(void)
{
    /* After the tx has been processed, we need to free the packet/character allocation */
    uint16_t enqueued = 0;
    uint16_t i = tx_last_seen_used;
    uint16_t curr_idx = tx_virtq.used->idx;

    while (i != curr_idx) {
        struct virtq_used_elem pkt_used = tx_virtq.used->ring[i % tx_virtq.num];
        struct virtq_desc pkt = tx_virtq.desc[pkt_used.id];

        uint64_t addr = pkt.addr;

        /* Free the packet */
        int err = ialloc_free(&tx_ialloc_desc, pkt_used.id);
        assert(!err);

        /* Free the character */
        int char_idx = addr - virtio_tx_char_paddr;
        err = ialloc_free(&tx_char_ialloc_desc, char_idx);
        assert(!err);

        tx_last_desc_idx -= 1;
        assert(tx_last_desc_idx >= 0);
        i++;

        enqueued++;
    }

    tx_last_seen_used += enqueued;
}

static void rx_provide(void)
{
    /* Fill up the virtio available ring buffer */
    bool transferred = false;
    while (!virtio_avail_full_rx(&rx_virtq)) {
        // Allocate a desc entry for the packet and the character
        uint32_t pkt_desc_idx = -1;
        int err = ialloc_alloc(&rx_ialloc_desc, &pkt_desc_idx);
        assert(!err && pkt_desc_idx != -1);

        uint32_t char_idx = -1;
        err = ialloc_alloc(&rx_char_ialloc_desc, &char_idx);
        assert(!err && char_idx != -1);

        assert(pkt_desc_idx < rx_virtq.num);
        assert(char_idx < rx_virtq.num);

        /* The packet will point to the memory we have reserved for the character */
        rx_virtq.desc[pkt_desc_idx].addr = virtio_rx_char_paddr + char_idx;
        rx_virtq.desc[pkt_desc_idx].len = 1;
        rx_virtq.desc[pkt_desc_idx].flags = VIRTQ_DESC_F_WRITE;

        // Set the entry in the available ring to point to the descriptor entry fort he packet
        rx_virtq.avail->ring[rx_virtq.avail->idx % rx_virtq.num] = pkt_desc_idx;
        rx_virtq.avail->idx++;
        rx_last_desc_idx += 1;

        transferred = true;
    }

    if (transferred) {
        /* We have added more avail buffers, so notify the device */
        uart_regs->QueueNotify = VIRTIO_SERIAL_RX_QUEUE;
    }
}

static void rx_return(void)
{
    /* Extract RX buffers from the 'used' and pass them up to the client by putting them
     * in the sDDF receive queue. */
    uint16_t transferred = 0;
    uint16_t i = rx_last_seen_used;
    uint16_t curr_idx = rx_virtq.used->idx;
    bool reprocess = true;

    while (reprocess) {
        while (i != curr_idx && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            struct virtq_used_elem pkt_used = rx_virtq.used->ring[i % rx_virtq.num];
            struct virtq_desc pkt = rx_virtq.desc[pkt_used.id];

            uint64_t addr = pkt.addr;
            assert(!(pkt.flags & VIRTQ_DESC_F_NEXT));

            uint32_t char_idx = addr - virtio_rx_char_paddr;
            serial_enqueue(&rx_queue_handle, virtio_rx_char[char_idx]);

                /* Free the packet descriptor */
            int err = ialloc_free(&rx_ialloc_desc, pkt_used.id);
            assert(!err);

                /* Free the character */
            err = ialloc_free(&rx_char_ialloc_desc, char_idx);
            assert(!err);

            rx_last_desc_idx -= 1;
            assert(rx_last_desc_idx >= 0);
            i++;
            transferred++;
        }

        if (i != curr_idx && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_request_consumer_signal(&rx_queue_handle);
        }
        reprocess = false;

        if (i != curr_idx && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }

    rx_last_seen_used += transferred;

    if (transferred > 0) {
        microkit_notify(config.rx.id);
    }
}

void console_setup()
{
    if (!virtio_mmio_check_magic(uart_regs)) {
        LOG_DRIVER_ERR("invalid virtIO magic value!\n");
        return;
    }

    if (!virtio_mmio_check_device_id(uart_regs, VIRTIO_DEVICE_ID_CONSOLE)) {
        LOG_DRIVER_ERR("Not a virtIO console device!\n");
        return;
    }

    if (virtio_mmio_version(uart_regs) != VIRTIO_VERSION) {
        LOG_DRIVER_ERR("not correct virtIO version!\n");
        return;
    }

    LOG_DRIVER("version: 0x%x\n", virtio_mmio_version(uart_regs));

    // Do normal device initialisation (section 3.2)
    // First reset the device
    uart_regs->Status = 0;

    // Set the ACKNOWLEDGE bit to say we have noticed the device
    uart_regs->Status = VIRTIO_DEVICE_STATUS_ACKNOWLEDGE;

        // Set the DRIVER bit to say we know how to drive the device
    uart_regs->Status = VIRTIO_DEVICE_STATUS_DRIVER;

#ifdef DEBUG_DRIVER
    uint32_t features_low = uart_regs->DeviceFeatures;
    uart_regs->DeviceFeaturesSel = 1;
    uint32_t features_high = uart_regs->DeviceFeatures;
    uint64_t features = features_low | ((uint64_t)features_high << 32);
    virtio_console_print_features(features);
#endif /* DEBUG_DRIVER */

    uart_regs->Status = VIRTIO_DEVICE_STATUS_FEATURES_OK;

    if (!(uart_regs->Status & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_DRIVER_ERR("device status features is not OK!\n");
        return;
    }

    // Setup the virtqueues
    size_t rx_desc_off = 0;
    size_t rx_avail_off = ALIGN(rx_desc_off + (16 * RX_COUNT), 2);
    size_t rx_used_off = ALIGN(rx_avail_off + (6 + 2 * RX_COUNT), 4);
    size_t tx_desc_off = ALIGN(rx_used_off + (6 + 8 * RX_COUNT), 16);
    size_t tx_avail_off = ALIGN(tx_desc_off + (16 * TX_COUNT), 2);
    size_t tx_used_off = ALIGN(tx_avail_off + (6 + 2 * TX_COUNT), 4);

    rx_virtq.num = RX_COUNT;
    rx_virtq.desc = (struct virtq_desc *)(hw_ring_buffer_vaddr + rx_desc_off);
    rx_virtq.avail = (struct virtq_avail *)(hw_ring_buffer_vaddr + rx_avail_off);
    rx_virtq.used = (struct virtq_used *)(hw_ring_buffer_vaddr + rx_used_off);

    assert((uintptr_t)rx_virtq.desc % 16 == 0);
    assert((uintptr_t)rx_virtq.avail % 2 == 0);
    assert((uintptr_t)rx_virtq.used % 4 == 0);

    tx_virtq.num = TX_COUNT;
    tx_virtq.desc = (struct virtq_desc *)(hw_ring_buffer_vaddr + tx_desc_off);
    tx_virtq.avail = (struct virtq_avail *)(hw_ring_buffer_vaddr + tx_avail_off);
    tx_virtq.used = (struct virtq_used *)(hw_ring_buffer_vaddr + tx_used_off);

    assert((uintptr_t)tx_virtq.desc % 16 == 0);
    assert((uintptr_t)tx_virtq.avail % 2 == 0);
    assert((uintptr_t)tx_virtq.used % 4 == 0);

    /* Load the Rx queue with free buffers */
    rx_provide();

    // Setup RX queue first
    assert(uart_regs->QueueNumMax >= RX_COUNT);
    uart_regs->QueueSel = VIRTIO_SERIAL_RX_QUEUE;
    uart_regs->QueueNum = RX_COUNT;
    uart_regs->QueueDescLow = (hw_ring_buffer_paddr + rx_desc_off) & 0xFFFFFFFF;
    uart_regs->QueueDescHigh = (hw_ring_buffer_paddr + rx_desc_off) >> 32;
    uart_regs->QueueDriverLow = (hw_ring_buffer_paddr + rx_avail_off) & 0xFFFFFFFF;
    uart_regs->QueueDriverHigh = (hw_ring_buffer_paddr + rx_avail_off) >> 32;
    uart_regs->QueueDeviceLow = (hw_ring_buffer_paddr + rx_used_off) & 0xFFFFFFFF;
    uart_regs->QueueDeviceHigh = (hw_ring_buffer_paddr + rx_used_off) >> 32;
    uart_regs->QueueReady = 1;

    // Setup TX queue
    assert(uart_regs->QueueNumMax >= TX_COUNT);
    uart_regs->QueueSel = VIRTIO_SERIAL_TX_QUEUE;
    uart_regs->QueueNum = TX_COUNT;
    uart_regs->QueueDescLow = (hw_ring_buffer_paddr + tx_desc_off) & 0xFFFFFFFF;
    uart_regs->QueueDescHigh = (hw_ring_buffer_paddr + tx_desc_off) >> 32;
    uart_regs->QueueDriverLow = (hw_ring_buffer_paddr + tx_avail_off) & 0xFFFFFFFF;
    uart_regs->QueueDriverHigh = (hw_ring_buffer_paddr + tx_avail_off) >> 32;
    uart_regs->QueueDeviceLow = (hw_ring_buffer_paddr + tx_used_off) & 0xFFFFFFFF;
    uart_regs->QueueDeviceHigh = (hw_ring_buffer_paddr + tx_used_off) >> 32;
    uart_regs->QueueReady = 1;

    // Set the DRIVER_OK status bit
    uart_regs->Status = VIRTIO_DEVICE_STATUS_DRIVER_OK;
    uart_regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
}

static void handle_irq()
{
    uint32_t irq_status = uart_regs->InterruptStatus;
    if (irq_status & VIRTIO_MMIO_IRQ_VQUEUE) {
        // We don't know whether the IRQ is related to a change to the RX queue
        // or TX queue, so we check both.
        rx_return();
        rx_provide(); // Refill the virtio Rx queue
        tx_return();
        tx_provide();
        // We have handled the used buffer notification
        uart_regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
    }

    if (irq_status & VIRTIO_MMIO_IRQ_CONFIG) {
        LOG_DRIVER_ERR("unexpected change in configuration %u\n", irq_status);
    }
}

void init()
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 4);

    uart_regs = (volatile virtio_mmio_regs_t *)device_resources.regions[0].region.vaddr;
    hw_ring_buffer_vaddr = (uintptr_t)device_resources.regions[1].region.vaddr;
    hw_ring_buffer_paddr = device_resources.regions[1].io_addr;
    virtio_rx_char = device_resources.regions[2].region.vaddr;
    virtio_rx_char_paddr = device_resources.regions[2].io_addr;
    virtio_tx_char = device_resources.regions[3].region.vaddr;
    virtio_tx_char_paddr = device_resources.regions[3].io_addr;

    ialloc_init(&rx_ialloc_desc, rx_descriptors, RX_COUNT);
    ialloc_init(&tx_ialloc_desc, tx_descriptors, TX_COUNT);
    ialloc_init(&tx_char_ialloc_desc, tx_char_desc, TX_COUNT);
    ialloc_init(&rx_char_ialloc_desc, rx_char_desc, RX_COUNT);

    console_setup();

    if (config.rx_enabled) {
        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    microkit_irq_ack(device_resources.irqs[0].id);
}

void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        microkit_deferred_irq_ack(ch);
    } else if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else {
        LOG_DRIVER_ERR("received notification on unexpected channel: %u\n", ch);
    }
}
