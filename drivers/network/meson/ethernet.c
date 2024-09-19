/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
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

/* The same as Linux's default for pause frame timeout */
const uint32_t pause_time = 0xffff;

struct descriptor {
    uint32_t status;
    uint32_t cntl;
    uint32_t addr;
    uint32_t next;
};

_Static_assert((RX_COUNT + TX_COUNT) * sizeof(struct descriptor) <= NET_HW_REGION_SIZE,
               "Expect rx+tx buffers to fit in single 2MB page");

typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of the ring */
    volatile struct descriptor *descr; /* buffer descriptor array */
    net_buff_desc_t descr_mdata[MAX_COUNT]; /* associated meta data array */
} hw_ring_t;

hw_ring_t rx;
hw_ring_t tx;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

volatile struct eth_mac_regs *eth_mac;
volatile struct eth_dma_regs *eth_dma;

static inline bool hw_ring_full(hw_ring_t *ring)
{
    return ring->tail - ring->head == ring->capacity;
}

static inline bool hw_ring_empty(hw_ring_t *ring)
{
    return ring->tail - ring->head == 0;
}

static void update_ring_slot(hw_ring_t *ring, unsigned int idx, uint32_t status,
                             uint32_t cntl, uint32_t phys, uint32_t next)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->addr = phys;
    d->next = next;
    d->cntl = cntl;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    THREAD_MEMORY_RELEASE();
    d->status = status;
}

static void rx_provide()
{
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&rx) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint32_t idx = rx.tail % rx.capacity;
            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (idx + 1 == rx.capacity) {
                cntl |= DESC_RXCTRL_RXRINGEND;
            }

            rx.descr_mdata[idx] = buffer;
            update_ring_slot(&rx, idx, DESC_RXSTS_OWNBYDMA, cntl, buffer.io_or_offset, 0);
            eth_dma->rxpolldemand = POLL_DATA;

            rx.tail++;
        }

        net_request_signal_free(&rx_queue);
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
        if (d->status & DESC_RXSTS_OWNBYDMA) {
            break;
        }

        THREAD_MEMORY_ACQUIRE();

        net_buff_desc_t buffer = rx.descr_mdata[idx];
        if (d->status & DESC_RXSTS_ERROR) {
            sddf_dprintf("ETH|ERROR: RX descriptor returned with error status %x\n", d->status);
            idx = rx.tail % rx.capacity;
            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (idx + 1 == rx.capacity) {
                cntl |= DESC_RXCTRL_RXRINGEND;
            }

            rx.descr_mdata[idx] = buffer;
            update_ring_slot(&rx, idx, DESC_RXSTS_OWNBYDMA, cntl, buffer.io_or_offset, 0);
            eth_dma->rxpolldemand = POLL_DATA;
            rx.tail++;
        } else {
            buffer.len = (d->status & DESC_RXSTS_LENMSK) >> DESC_RXSTS_LENSHFT;
            int err = net_enqueue_active(&rx_queue, buffer);
            assert(!err);
            packets_transferred = true;
        }
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
            uint32_t cntl = (((uint32_t) buffer.len) << DESC_TXCTRL_SIZE1SHFT) & DESC_TXCTRL_SIZE1MASK;
            cntl |= DESC_TXCTRL_TXLAST | DESC_TXCTRL_TXFIRST | DESC_TXCTRL_TXINT;
            if (idx + 1 == tx.capacity) {
                cntl |= DESC_TXCTRL_TXRINGEND;
            }
            tx.descr_mdata[idx] = buffer;
            update_ring_slot(&tx, idx, DESC_TXSTS_OWNBYDMA, cntl, buffer.io_or_offset, 0);

            tx.tail++;
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_ring_full(&tx) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }
    eth_dma->txpolldemand = POLL_DATA;
}

static void tx_return(void)
{
    bool enqueued = false;
    while (!hw_ring_empty(&tx)) {
        /* Ensure that this buffer has been sent by the device */
        uint32_t idx = tx.head % tx.capacity;
        volatile struct descriptor *d = &(tx.descr[idx]);
        if (d->status & DESC_TXSTS_OWNBYDMA) {
            break;
        }

        THREAD_MEMORY_ACQUIRE();

        net_buff_desc_t buffer = tx.descr_mdata[idx];
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

static void handle_irq()
{
    uint32_t e = eth_dma->status;
    eth_dma->status &= e;

    while(e & DMA_INTR_NORMAL) {
        if (e & DMA_INTR_RXF) {
            rx_return();
            rx_provide();
        }
        if (e & DMA_INTR_TXF) {
            tx_return();
            tx_provide();
        }
        if (e & DMA_INTR_ABNORMAL) {
            if (e & DMA_INTR_FBE) {
                sddf_dprintf("Ethernet device fatal bus error\n");
            }
        }
        e = eth_dma->status;
        eth_dma->status &= e;
    }
}

static void eth_setup(void)
{
    eth_dma = (void *)((uintptr_t)eth_mac + DMA_REG_OFFSET);
    uint32_t l = eth_mac->macaddr0lo;
    uint32_t h = eth_mac->macaddr0hi;

    assert((hw_ring_buffer_paddr & 0xFFFFFFFF) == hw_ring_buffer_paddr);

    rx.capacity = RX_COUNT;
    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx.capacity = TX_COUNT;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

    /* Perform reset */
    eth_dma->busmode |= DMAMAC_SWRST;
    while (eth_dma->busmode & DMAMAC_SWRST);

    /* Perform flush */
    eth_dma->opmode = FLUSHTXFIFO;
    while (eth_dma->opmode & FLUSHTXFIFO);

    /* Reset removes the mac address */
    eth_mac->macaddr0lo = l;
    eth_mac->macaddr0hi = h;

    eth_dma->busmode = PRIORXTX_11 | ((DMA_PBL << TX_PBL_SHFT) & TX_PBL_MASK);
    /*
     * Operate in store-and-forward mode.
     * Send pause frames when there's only 1k of fifo left,
     * stop sending them when there is 2k of fifo left.
     * Continue DMA on 2nd frame while updating status on first
     */
    eth_dma->opmode = STOREFORWARD | EN_FLOWCTL | (0 << FLOWCTL_SHFT) | (1 < DISFLOWCTL_SHFT) | TX_OPSCND;
    eth_mac->conf = FULLDPLXMODE;

    eth_dma->rxdesclistaddr = hw_ring_buffer_paddr;
    eth_dma->txdesclistaddr = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);

    eth_mac->framefilt |= PMSCUOUS_MODE;

    uint32_t flow_ctrl = GMAC_FLOW_CTRL_UP | GMAC_FLOW_CTRL_RFE | GMAC_FLOW_CTRL_TFE;
    flow_ctrl |= (pause_time << GMAC_FLOW_CTRL_PT_SHIFT);
    eth_mac->flowcontrol = flow_ctrl;
}

void init(void)
{
    eth_setup();

    net_queue_init(&rx_queue, (net_queue_t *)rx_free, (net_queue_t *)rx_active, NET_RX_QUEUE_CAPACITY_DRIV);
    net_queue_init(&tx_queue, (net_queue_t *)tx_free, (net_queue_t *)tx_active, NET_TX_QUEUE_CAPACITY_DRIV);

    rx_provide();
    tx_provide();

    /* Enable IRQs */
    eth_dma->intenable |= DMA_INTR_MASK;

    /* Disable uneeded GMAC irqs */
    eth_mac->intmask |= GMAC_INTR_MASK;

    /* We are ready to receive. Enable. */
    eth_mac->conf |= RX_ENABLE | TX_ENABLE;
    eth_dma->opmode |= TXSTART | RXSTART;

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
        sddf_dprintf("ETH|LOG: received notification on unexpected channel %u\n", ch);
        break;
    }
}
