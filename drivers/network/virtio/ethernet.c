/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * This driver follows the non-legacy virtIO 1.2 specification for the network device.
 * It assumes that the transport method is MMIO.
 * This driver is very minimal and was written for the goal of building systems that
 * use networking on a simulator like QEMU. It is *not* intended to be performant.
 *
 * It should also be noted that because this driver is intended to be used with a
 * simulator such as QEMU, things like memory fences when touching device registers
 * may be needed if instead this driver was to be used in a different environment.
 */
#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/ialloc.h>
#include <sddf/virtio/virtio.h>
#include <sddf/virtio/virtio_queue.h>
#include <ethernet_config.h>

#include "ethernet.h"

/*
 * This default is based on the default QEMU setup but could change
 * depending on the instantiation of QEMU or wherever this driver is
 * being used.
 */
#ifndef VIRTIO_MMIO_NET_OFFSET
#define VIRTIO_MMIO_NET_OFFSET (0xe00)
#endif

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

uintptr_t eth_regs;
/*
 * The 'hardware' ring buffer region is used to store the virtIO virtqs
 * as well as the RX and TX virtIO headers.
 */
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

net_queue_t *rx_free;
net_queue_t *rx_active;
net_queue_t *tx_free;
net_queue_t *tx_active;

#define RX_COUNT 512
#define TX_COUNT 512
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

#define HW_RING_SIZE (0x10000)

struct virtq rx_virtq;
struct virtq tx_virtq;
uint16_t rx_last_seen_used = 0;
uint16_t tx_last_seen_used = 0;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

/*
 * This driver has no use of the virtIO net headers that go before
 * each packet. Our policy is to discard them when we get RX and
 * initialise to the default values on TX. In order to this, we use a
 * separate memory region and not the sDDF data region.
 */
uintptr_t virtio_net_tx_headers_vaddr;
uintptr_t virtio_net_tx_headers_paddr;
uintptr_t virtio_net_rx_headers_paddr;
virtio_net_hdr_t *virtio_net_tx_headers;

volatile virtio_mmio_regs_t *regs;

ialloc_t rx_ialloc_desc;
uint32_t rx_descriptors[RX_COUNT];
ialloc_t tx_ialloc_desc;
uint32_t tx_descriptors[TX_COUNT];

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

static void rx_provide(void)
{
    /* We need to take all of our sDDF free entries and place them in the virtIO 'free' ring. */
    bool transferred = false;
    bool reprocess = true;
    while (reprocess) {
        while (!virtio_avail_full_rx(&rx_virtq) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            // Allocate a desc entry for the header, and one for the packet
            uint32_t hdr_desc_idx = -1;
            err = ialloc_alloc(&rx_ialloc_desc, &hdr_desc_idx);
            assert(!err && hdr_desc_idx != -1);
            uint32_t pkt_desc_idx = -1;
            err = ialloc_alloc(&rx_ialloc_desc, &pkt_desc_idx);
            assert(!err && pkt_desc_idx != -1);

            assert(hdr_desc_idx < rx_virtq.num);
            assert(pkt_desc_idx < rx_virtq.num);

            // Get the header address, which is an index into the virtio net headers memory region
            rx_virtq.desc[hdr_desc_idx].addr = virtio_net_rx_headers_paddr + (hdr_desc_idx * sizeof(virtio_net_hdr_t));
            rx_virtq.desc[hdr_desc_idx].len = sizeof(virtio_net_hdr_t);
            // Set the next of the header to the packet
            rx_virtq.desc[hdr_desc_idx].next = pkt_desc_idx;
            rx_virtq.desc[hdr_desc_idx].flags = VIRTQ_DESC_F_NEXT | VIRTQ_DESC_F_WRITE;
            // The packet address will be the actual buffer that we have dequeued from the client
            rx_virtq.desc[pkt_desc_idx].addr = buffer.io_or_offset;
            rx_virtq.desc[pkt_desc_idx].len = NET_BUFFER_SIZE;
            rx_virtq.desc[pkt_desc_idx].flags = VIRTQ_DESC_F_WRITE;
            // Set the entry in the available ring to point to the desc entry for the header
            rx_virtq.avail->ring[rx_virtq.avail->idx % rx_virtq.num] = hdr_desc_idx;
            // We only want to increment the avail ring by 1, as we are only increasing by one in
            // this list, but we are adding two desc entries.
            rx_virtq.avail->idx++;
            rx_last_desc_idx += 2;

            transferred = true;
        }

        net_request_signal_free(&rx_queue);
        reprocess = false;

        if (!net_queue_empty_free(&rx_queue) && !virtio_avail_full_rx(&rx_virtq)) {
            net_cancel_signal_free(&rx_queue);
            reprocess = true;
        }
    }

    if (transferred) {
        /* We have added more avail buffers, so notify the device */
        regs->QueueNotify = VIRTIO_NET_RX_QUEUE;
    }
}

static void rx_return(void)
{
    /* Extract RX buffers from the 'used' and pass them up to the client by putting them
     * in our sDDF 'active' queues. */
    uint16_t packets_transferred = 0;
    uint16_t i = rx_last_seen_used;
    uint16_t curr_idx = rx_virtq.used->idx;
    while (i != curr_idx) {
        LOG_DRIVER("i: 0x%lx\n", i);
        struct virtq_used_elem hdr_used = rx_virtq.used->ring[i % rx_virtq.num];
        assert(rx_virtq.desc[hdr_used.id].flags & VIRTQ_DESC_F_NEXT);

        struct virtq_desc pkt = rx_virtq.desc[rx_virtq.desc[hdr_used.id].next % rx_virtq.num];
        uint64_t addr = pkt.addr;
        uint32_t len = pkt.len;
        assert(!(pkt.flags & VIRTQ_DESC_F_NEXT));

        net_buff_desc_t buffer = { addr, len };
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        err = ialloc_free(&rx_ialloc_desc, hdr_used.id);
        assert(!err);
        err = ialloc_free(&rx_ialloc_desc, rx_virtq.desc[hdr_used.id].next);
        assert(!err);

        rx_last_desc_idx -= 2;
        assert(rx_last_desc_idx >= 0);
        i++;
        packets_transferred++;
    }
    rx_last_seen_used += packets_transferred;

    if (packets_transferred > 0 && net_require_signal_active(&rx_queue)) {
        LOG_DRIVER("signalling RX\n");
        net_cancel_signal_active(&rx_queue);
        microkit_notify(RX_CH);
    }
}

static void tx_provide(void)
{
    bool reprocess = true;
    bool packets_transferred = false;
    while (reprocess) {
        while (!virtio_avail_full_tx(&tx_virtq) && !net_queue_empty_active(&tx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            /* Now we need to put our buffer into the virtIO ring */
            uint32_t hdr_desc_idx = -1;
            err = ialloc_alloc(&tx_ialloc_desc, &hdr_desc_idx);
            assert(!err && hdr_desc_idx != -1);
            uint32_t pkt_desc_idx = -1;
            err = ialloc_alloc(&tx_ialloc_desc, &pkt_desc_idx);
            assert(!err && pkt_desc_idx != -1);
            /* We should not run out of descriptors assuming that the avail ring is not full. */
            assert(hdr_desc_idx < tx_virtq.num);
            assert(pkt_desc_idx < tx_virtq.num);
            tx_virtq.avail->ring[tx_virtq.avail->idx % tx_virtq.num] = hdr_desc_idx;

            virtio_net_hdr_t *hdr = &virtio_net_tx_headers[hdr_desc_idx];
            hdr->flags = 0;
            hdr->gso_type = VIRTIO_NET_HDR_GSO_NONE;
            hdr->hdr_len = 0;  /* not used unless we have segmentation offload */
            hdr->gso_size = 0; /* same */
            hdr->csum_start = 0;
            hdr->csum_offset = 0;
            tx_virtq.desc[hdr_desc_idx].addr = virtio_net_tx_headers_paddr + (hdr_desc_idx * sizeof(virtio_net_hdr_t));
            tx_virtq.desc[hdr_desc_idx].len = sizeof(virtio_net_hdr_t);
            tx_virtq.desc[hdr_desc_idx].next = pkt_desc_idx;
            tx_virtq.desc[hdr_desc_idx].flags = VIRTQ_DESC_F_NEXT;
            tx_virtq.desc[pkt_desc_idx].addr = buffer.io_or_offset;
            tx_virtq.desc[pkt_desc_idx].len = buffer.len;
            tx_virtq.desc[pkt_desc_idx].flags = 0;

            tx_virtq.avail->idx++;
            tx_last_desc_idx += 2;

            packets_transferred = true;
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!virtio_avail_full_tx(&tx_virtq) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }

    if (packets_transferred) {
        /* Finally, need to notify the queue if we have transferred data */
        /* This assumes VIRTIO_F_NOTIFICATION_DATA has not been negotiated */
        regs->QueueNotify = VIRTIO_NET_TX_QUEUE;
    }
}

static void tx_return(void)
{
    /* We must look through the 'used' ring of the TX virtqueue and place them in our
     * sDDF TX free queue. */
    uint16_t enqueued = 0;
    uint16_t i = tx_last_seen_used;
    uint16_t curr_idx = tx_virtq.used->idx;
    while (i != curr_idx && !net_queue_full_free(&tx_queue)) {
        /* For each TX free entry in the sDDF queue, there are *two* virtq used entries.
         * One for the virtIO header, and one for the packet. */
        struct virtq_used_elem hdr_used = tx_virtq.used->ring[i % tx_virtq.num];

        assert(tx_virtq.desc[hdr_used.id].flags & VIRTQ_DESC_F_NEXT);

        struct virtq_desc pkt = tx_virtq.desc[tx_virtq.desc[hdr_used.id].next % tx_virtq.num];
        uint64_t addr = pkt.addr;
        assert(!(pkt.flags & VIRTQ_DESC_F_NEXT));

        net_buff_desc_t buffer = { addr, 0 };
        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);

        err = ialloc_free(&tx_ialloc_desc, hdr_used.id);
        assert(!err);
        err = ialloc_free(&tx_ialloc_desc, tx_virtq.desc[hdr_used.id].next);
        assert(!err);
        tx_last_desc_idx -= 2;
        assert(tx_last_desc_idx >= 0);
        i++;

        enqueued++;
    }

    tx_last_seen_used += enqueued;

    if (enqueued > 0 && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(TX_CH);
    }
}

static void handle_irq()
{
    uint32_t irq_status = regs->InterruptStatus;
    if (irq_status & VIRTIO_MMIO_IRQ_VQUEUE) {
        // We don't know whether the IRQ is related to a change to the RX queue
        // or TX queue, so we check both.
        rx_return();
        tx_return();
        tx_provide();
        // We have handled the used buffer notification
        regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
    }

    if (irq_status & VIRTIO_MMIO_IRQ_CONFIG) {
        LOG_DRIVER_ERR("ETH|ERROR: unexpected change in configuration %u\n", irq_status);
    }
}

static void eth_setup(void)
{
    // Do MMIO device init (section 4.2.3.1)
    if (!virtio_mmio_check_magic(regs)) {
        LOG_DRIVER_ERR("invalid virtIO magic value!\n");
        assert(false);
    }

    if (virtio_mmio_version(regs) != VIRTIO_VERSION) {
        LOG_DRIVER_ERR("not correct virtIO version!\n");
        assert(false);
    }

    if (!virtio_mmio_check_device_id(regs, VIRTIO_DEVICE_ID_NET)) {
        LOG_DRIVER_ERR("not a virtIO network device!\n");
        assert(false);
    }

    LOG_DRIVER("version: 0x%x\n", virtio_mmio_version(regs));

    // Do normal device initialisation (section 3.2)

    // First reset the device
    regs->Status = 0;

    // Set the ACKNOWLEDGE bit to say we have noticed the device
    regs->Status = VIRTIO_DEVICE_STATUS_ACKNOWLEDGE;
    // Set the DRIVER bit to say we know how to drive the device
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER;

#ifdef DEBUG_DRIVER
    uint32_t feature_low = regs->DeviceFeatures;
    regs->DeviceFeaturesSel = 1;
    uint32_t feature_high = regs->DeviceFeatures;
    uint64_t feature = feature_low | ((uint64_t)feature_high << 32);
    virtio_net_print_features(feature);
#endif

    regs->DriverFeatures = VIRTIO_NET_F_MAC;
    regs->DriverFeaturesSel = 1;
    regs->DriverFeatures = VIRTIO_F_VERSION_1;

    regs->Status = VIRTIO_DEVICE_STATUS_FEATURES_OK;

    if (!(regs->Status & VIRTIO_DEVICE_STATUS_FEATURES_OK)) {
        LOG_DRIVER_ERR("device status features is not OK!\n");
        return;
    }

    volatile virtio_net_config_t *config = (virtio_net_config_t *)regs->Config;
#ifdef DEBUG_DRIVER
    virtio_net_print_config(config);
#endif

    // Setup the virtqueues

    size_t rx_desc_off = 0;
    size_t rx_avail_off = ALIGN(rx_desc_off + (16 * RX_COUNT), 2);
    size_t rx_used_off = ALIGN(rx_avail_off + (6 + 2 * RX_COUNT), 4);
    size_t tx_desc_off = ALIGN(rx_used_off + (6 + 8 * RX_COUNT), 16);
    size_t tx_avail_off = ALIGN(tx_desc_off + (16 * TX_COUNT), 2);
    size_t tx_used_off = ALIGN(tx_avail_off + (6 + 2 * TX_COUNT), 4);
    size_t virtq_size = tx_used_off + (6 + 8 * TX_COUNT);

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

    /* Virtio TX headers will proceed the virtq structures. Then RX headers. */
    virtio_net_tx_headers_vaddr = hw_ring_buffer_vaddr + virtq_size;
    virtio_net_tx_headers_paddr = hw_ring_buffer_paddr + virtq_size;
    virtio_net_tx_headers = (virtio_net_hdr_t *) virtio_net_tx_headers_vaddr;
    size_t tx_headers_size = ((TX_COUNT / 2) * sizeof(virtio_net_hdr_t));
    virtio_net_rx_headers_paddr = virtio_net_tx_headers_paddr + tx_headers_size;
    size_t rx_headers_size = ((RX_COUNT / 2) * sizeof(virtio_net_hdr_t));

    assert(virtq_size + tx_headers_size + rx_headers_size <= HW_RING_SIZE);

    rx_provide();
    tx_provide();

    // Setup RX queue first
    assert(regs->QueueNumMax >= RX_COUNT);
    regs->QueueSel = VIRTIO_NET_RX_QUEUE;
    regs->QueueNum = RX_COUNT;
    regs->QueueDescLow = (hw_ring_buffer_paddr + rx_desc_off) & 0xFFFFFFFF;
    regs->QueueDescHigh = (hw_ring_buffer_paddr + rx_desc_off) >> 32;
    regs->QueueDriverLow = (hw_ring_buffer_paddr + rx_avail_off) & 0xFFFFFFFF;
    regs->QueueDriverHigh = (hw_ring_buffer_paddr + rx_avail_off) >> 32;
    regs->QueueDeviceLow = (hw_ring_buffer_paddr + rx_used_off) & 0xFFFFFFFF;
    regs->QueueDeviceHigh = (hw_ring_buffer_paddr + rx_used_off) >> 32;
    regs->QueueReady = 1;

    // Setup TX queue
    assert(regs->QueueNumMax >= TX_COUNT);
    regs->QueueSel = VIRTIO_NET_TX_QUEUE;
    regs->QueueNum = TX_COUNT;
    regs->QueueDescLow = (hw_ring_buffer_paddr + tx_desc_off) & 0xFFFFFFFF;
    regs->QueueDescHigh = (hw_ring_buffer_paddr + tx_desc_off) >> 32;
    regs->QueueDriverLow = (hw_ring_buffer_paddr + tx_avail_off) & 0xFFFFFFFF;
    regs->QueueDriverHigh = (hw_ring_buffer_paddr + tx_avail_off) >> 32;
    regs->QueueDeviceLow = (hw_ring_buffer_paddr + tx_used_off) & 0xFFFFFFFF;
    regs->QueueDeviceHigh = (hw_ring_buffer_paddr + tx_used_off) >> 32;
    regs->QueueReady = 1;

    // Set the MAC address
    config->mac[0] = 0x52;
    config->mac[1] = 0x54;
    config->mac[2] = 0x01;
    config->mac[3] = 0x00;
    config->mac[4] = 0x00;
    config->mac[5] = 0x07;

    // Set the DRIVER_OK status bit
    regs->Status = VIRTIO_DEVICE_STATUS_DRIVER_OK;
    regs->InterruptACK = VIRTIO_MMIO_IRQ_VQUEUE;
}

void init(void)
{
    regs = (volatile virtio_mmio_regs_t *)(eth_regs + VIRTIO_MMIO_NET_OFFSET);

    ialloc_init(&rx_ialloc_desc, rx_descriptors, RX_COUNT);
    ialloc_init(&tx_ialloc_desc, tx_descriptors, TX_COUNT);

    net_queue_init(&rx_queue, rx_free, rx_active, NET_RX_QUEUE_CAPACITY_DRIV);
    net_queue_init(&tx_queue, tx_free, tx_active, NET_TX_QUEUE_CAPACITY_DRIV);

    eth_setup();

    microkit_irq_ack(IRQ_CH);
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case IRQ_CH:
        handle_irq();
        microkit_deferred_irq_ack(ch);
        break;
    case RX_CH:
        rx_provide();
        break;
    case TX_CH:
        tx_provide();
        break;
    default:
        LOG_DRIVER_ERR("received notification on unexpected channel %u\n", ch);
        break;
    }
}
