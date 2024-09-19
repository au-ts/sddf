/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#include "ethernet.h"

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

net_queue_t *rx_free;
net_queue_t *rx_active;
net_queue_t *tx_free;
net_queue_t *tx_active;

#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

_Static_assert((RX_COUNT + TX_COUNT) * 2 * NET_BUFFER_SIZE <= NET_DATA_REGION_SIZE,
               "Expect rx+tx buffers to fit in single 2MB page");

/* HW ring descriptor (shared with device) */
struct descriptor {
    uint16_t len;
    uint16_t stat;
    uint32_t addr;
};

/* HW ring buffer data type */
typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of the ring */
    volatile struct descriptor *descr; /* buffer descriptor array */
    net_buff_desc_t descr_mdata[MAX_COUNT]; /* associated meta data array */
} hw_ring_t;

hw_ring_t rx; /* Rx NIC ring */
hw_ring_t tx; /* Tx NIC ring */

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

#define MAX_PACKET_SIZE     1536

volatile struct enet_regs *eth;

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
    THREAD_MEMORY_RELEASE();
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
            rx.descr_mdata[idx] = buffer;
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

        THREAD_MEMORY_ACQUIRE();

        net_buff_desc_t buffer = rx.descr_mdata[idx];
        buffer.len = d->len;
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        packets_transferred = true;
        rx.head++;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(RX_CH);
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
            tx.descr_mdata[idx] = buffer;
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

        THREAD_MEMORY_ACQUIRE();

        net_buff_desc_t buffer = tx.descr_mdata[idx];
        buffer.len = 0;
        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);

        enqueued = true;
        tx.head++;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(TX_CH);
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
            sddf_dprintf("ETH|ERROR: System bus/uDMA\n");
        }
        e = eth->eir & IRQ_MASK;
        eth->eir = e;
    }
}

static void eth_setup(void)
{
    uint32_t l = eth->palr;
    uint32_t h = eth->paur;

    /* Set up HW rings */
    rx.capacity = RX_COUNT;
    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx.capacity = TX_COUNT;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

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

    eth->rdsr = hw_ring_buffer_paddr;
    eth->tdsr = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);

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
    eth_setup();

    net_queue_init(&rx_queue, rx_free, rx_active, NET_RX_QUEUE_CAPACITY_DRIV);
    net_queue_init(&tx_queue, tx_free, tx_active, NET_TX_QUEUE_CAPACITY_DRIV);

    rx_provide();
    tx_provide();
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case IRQ_CH:
        handle_irq();
        /*
         * Delay calling into the kernel to ack the IRQ until the next loop
         * in the microkit event handler loop.
         */
        microkit_deferred_irq_ack(ch);
        break;
    case RX_CH:
        rx_provide();
        break;
    case TX_CH:
        tx_provide();
        break;
    default:
        sddf_dprintf("ETH|LOG: received notification on unexpected channel: %u\n", ch);
        break;
    }
}
