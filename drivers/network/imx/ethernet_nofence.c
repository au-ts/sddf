/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>

#include "ethernet.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

__attribute__((__section__(".net_driver_config"))) net_driver_config_t config;

/* HW ring capacity must be a power of 2 */
#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

/* HW ring descriptor (shared with device) */
struct descriptor {
    uint16_t len;
    uint16_t stat;
    uint32_t addr;
};

/* HW ring buffer data type */
typedef struct {
#ifdef PANCAKE_NETWORK_DRIVER
    /* to avoid bit-shift operations, we try to use word size variables when possible in Pancake */
    uint64_t tail; /* index to insert at */
    uint64_t head; /* index to remove from */
    uint64_t capacity; /* capacity of the ring */
#else
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of the ring */
#endif
    volatile struct descriptor *descr; /* buffer descriptor array */
} hw_ring_t;

#ifdef PANCAKE_NETWORK_DRIVER
hw_ring_t *rx;
hw_ring_t *tx;

net_queue_handle_t *rx_queue;
net_queue_handle_t *tx_queue;
#else
hw_ring_t rx; /* Rx NIC ring */
hw_ring_t tx; /* Tx NIC ring */

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;
#endif

#define MAX_PACKET_SIZE     1536

volatile struct enet_regs *eth;

#ifdef PANCAKE_NETWORK_DRIVER
static char cml_memory[1024*8];
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern void cml_main(void);

void cml_exit(int arg) {
    microkit_dbg_puts("ERROR! We should not be getting here\n");
}

void cml_err(int arg) {
    if (arg == 3) {
        microkit_dbg_puts("Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
    }
  cml_exit(arg);
}

/* Need to come up with a replacement for this clear cache function.
    Might be worth testing just flushing the entire l1 cache,
    but might cause issues with returning to this file
*/
void cml_clear() {
    microkit_dbg_puts("Trying to clear cache\n");
}

void init_pancake_mem() {
    unsigned long cml_heap_sz = 1024*4;
    unsigned long cml_stack_sz = 1024*4;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;
}
#endif

#ifndef PANCAKE_NETWORK_DRIVER
static inline bool hw_ring_full(hw_ring_t *ring)
{
    return ring->tail - ring->head == ring->capacity;
}

static inline bool hw_ring_empty(hw_ring_t *ring)
{
    return ring->tail - ring->head == 0;
}

static void update_ring_slot(hw_ring_t *ring, unsigned int idx, uintptr_t phys,
                             uint16_t len, uint16_t stat)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->addr = phys;
    d->len = len;

    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    d->stat = stat;
}

static void rx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&rx) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint32_t idx = rx.tail % rx.capacity;
            uint16_t stat = RXD_EMPTY;
            if (idx + 1 == rx.capacity) {
                stat |= WRAP;
            }
            update_ring_slot(&rx, idx, buffer.io_or_offset, 0, stat);
            rx.tail++;
            eth->rdar = RDAR_RDAR;
        }

        /* Only request a notification from virtualiser if HW ring not full */
        if (!hw_ring_full(&rx)) {
            net_request_signal_free(&rx_queue);
        } else {
            net_cancel_signal_free(&rx_queue);
        }
        reprocess = false;

        if (!net_queue_empty_free(&rx_queue) && !hw_ring_full(&rx)) {
            net_cancel_signal_free(&rx_queue);
            reprocess = true;
        }
    }
}

static void rx_return(void)
{
    bool packets_transferred = false;
    while (!hw_ring_empty(&rx)) {
        /* If buffer slot is still empty, we have processed all packets the device has filled */
        uint32_t idx = rx.head % rx.capacity;
        volatile struct descriptor *d = &(rx.descr[idx]);
        if (d->stat & RXD_EMPTY) {
            break;
        }

        net_buff_desc_t buffer = { d->addr, d->len };
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        packets_transferred = true;
        rx.head++;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(config.virt_rx.id);
    }
}

static void tx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!(hw_ring_full(&tx)) && !net_queue_empty_active(&tx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            uint32_t idx = tx.tail % tx.capacity;
            uint16_t stat = TXD_READY | TXD_ADDCRC | TXD_LAST;
            if (idx + 1 == tx.capacity) {
                stat |= WRAP;
            }
            update_ring_slot(&tx, idx, buffer.io_or_offset, buffer.len, stat);
            tx.tail++;
            eth->tdar = TDAR_TDAR;
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_ring_full(&tx) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }
}

static void tx_return(void)
{
    bool enqueued = false;
    while (!hw_ring_empty(&tx)) {
        /* Ensure that this buffer has been sent by the device */
        uint32_t idx = tx.head % tx.capacity;
        volatile struct descriptor *d = &(tx.descr[idx]);
        if (d->stat & TXD_READY) {
            break;
        }

        net_buff_desc_t buffer = { d->addr, 0 };
        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);

        enqueued = true;
        tx.head++;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(config.virt_tx.id);
    }
}

static void handle_irq(void)
{
    uint32_t e = eth->eir & IRQ_MASK;
    eth->eir = e;

    while (e & IRQ_MASK) {
        if (e & NETIRQ_TXF) {
            tx_return();
            tx_provide();
        }
        if (e & NETIRQ_RXF) {
            rx_return();
            rx_provide();
        }
        if (e & NETIRQ_EBERR) {
            sddf_dprintf("ETH|ERROR: System bus/uDMA %u\n", e);
        }
        e = eth->eir & IRQ_MASK;
        eth->eir = e;
    }
}
#endif

static void eth_setup(void)
{
    eth = device_resources.regions[0].region.vaddr;

    uint32_t l = eth->palr;
    uint32_t h = eth->paur;

    /* Set up HW rings */
#ifdef PANCAKE_NETWORK_DRIVER
    rx->descr = (volatile struct descriptor *)device_resources.regions[1].region.vaddr;
    tx->descr = (volatile struct descriptor *)device_resources.regions[2].region.vaddr;
    rx->capacity = RX_COUNT;
    tx->capacity = TX_COUNT;
#else
    rx.descr = (volatile struct descriptor *)device_resources.regions[1].region.vaddr;
    tx.descr = (volatile struct descriptor *)device_resources.regions[2].region.vaddr;
    rx.capacity = RX_COUNT;
    tx.capacity = TX_COUNT;
#endif

    /* Perform reset */
    eth->ecr = ECR_RESET;
    while (eth->ecr & ECR_RESET);
    eth->ecr |= ECR_DBSWP;

    /* Clear and mask interrupts */
    eth->eimr = 0x00000000;
    eth->eir  = 0xffffffff;

    /* set MDIO freq */
    eth->mscr = 24 << 1;

    /* Disable */
    eth->mibc |= MIBC_DIS;
    while (!(eth->mibc & MIBC_IDLE));
    /* Clear */
    eth->mibc |= MIBC_CLEAR;
    while (!(eth->mibc & MIBC_IDLE));
    /* Restart */
    eth->mibc &= ~MIBC_CLEAR;
    eth->mibc &= ~MIBC_DIS;

    /* Descriptor group and individual hash tables - Not changed on reset */
    eth->iaur = 0;
    eth->ialr = 0;
    eth->gaur = 0;
    eth->galr = 0;

    /* Mac address needs setting again. */
    if (eth->palr == 0) {
        eth->palr = l;
        eth->paur = h;
    }

    eth->opd = PAUSE_OPCODE_FIELD;

    /* coalesce transmit IRQs to batches of 128 */
    eth->txic0 = ICEN | ICFT(128) | 0xFF;
    eth->tipg = TIPG;
    /* Transmit FIFO Watermark register - store and forward */
    eth->tfwr = STRFWD;
    /* clear rx store and forward. This must be done for hardware csums */
    eth->rsfl = 0;
    /* Do not forward frames with errors + check the csum */
    eth->racc = RACC_LINEDIS | RACC_IPDIS | RACC_PRODIS;
    /* Add the checksum for known IP protocols */
    eth->tacc = TACC_PROCHK | TACC_IPCHK;

    /* Set RDSR */
    eth->rdsr = device_resources.regions[1].io_addr;
    eth->tdsr = device_resources.regions[2].io_addr;

    /* Size of max eth packet size */
    eth->mrbr = MAX_PACKET_SIZE;

    eth->rcr = RCR_MAX_FL(1518) | RCR_RGMII_EN | RCR_MII_MODE | RCR_PROMISCUOUS;
    eth->tcr = TCR_FDEN;

    /* set speed */
    eth->ecr |= ECR_SPEED;

    /* Set Enable  in ECR */
    eth->ecr |= ECR_ETHEREN;

    eth->rdar = RDAR_RDAR;

    /* enable events */
    eth->eir = eth->eir;
    eth->eimr = IRQ_MASK;
}

void init(void)
{
    assert(net_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 3);
    // All buffers should fit within our DMA region
    assert(RX_COUNT * sizeof(struct descriptor) <= device_resources.regions[1].region.size);
    assert(TX_COUNT * sizeof(struct descriptor) <= device_resources.regions[2].region.size);

#ifdef PANCAKE_NETWORK_DRIVER
    init_pancake_mem();

    /* init_pancake_data */
    uintptr_t *pnk_mem = (uintptr_t *) cml_heap;

    /* Store constant info in Pancake memory */
    pnk_mem[1] = device_resources.irqs[0].id;
    pnk_mem[2] = config.virt_rx.id;
    pnk_mem[3] = config.virt_tx.id;

    /* Allocate global structs in Pancake memory */
    rx_queue = (net_queue_handle_t *) &pnk_mem[4];
    tx_queue = (net_queue_handle_t *) &pnk_mem[7];
    rx = (hw_ring_t *) &pnk_mem[10];
    tx = (hw_ring_t *) &pnk_mem[10 + sizeof(hw_ring_t)/sizeof(uintptr_t)];
#endif

    eth_setup();

#ifdef PANCAKE_NETWORK_DRIVER
    pnk_mem[0] = (uintptr_t) eth;

    net_queue_init(rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    cml_main();
#else
    net_queue_init(&rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    rx_provide();
    tx_provide();
#endif
}

#ifdef PANCAKE_NETWORK_DRIVER
extern void notified(microkit_channel ch);
#else
void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        /*
         * Delay calling into the kernel to ack the IRQ until the next loop
         * in the microkit event handler loop.
         */
        microkit_deferred_irq_ack(ch);
    } else if (ch == config.virt_rx.id) {
        rx_provide();
    } else if (ch == config.virt_tx.id) {
        tx_provide();
    } else {
        sddf_dprintf("ETH|LOG: received notification on unexpected channel: %u\n", ch);
    }
}
#endif
