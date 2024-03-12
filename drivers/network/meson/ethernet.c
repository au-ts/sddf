/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#include "ethernet.h"

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2
// #define IPBENCH_FINISH  3

uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;

#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

struct descriptor {
    uint32_t status;
    uint32_t cntl;
    uint32_t addr;
    uint32_t next;
};

_Static_assert((RX_COUNT + TX_COUNT) * sizeof(struct descriptor) <= HW_REGION_SIZE, "Expect rx+tx buffers to fit in single 2MB page");

typedef struct {
    unsigned int tail; /* index to insert at */
    unsigned int head; /* index to remove from */
    buff_desc_t descr_mdata[MAX_COUNT]; /* associated meta data array */
    volatile struct descriptor *descr; /* buffer descripter array */
} hw_ring_t;

hw_ring_t rx;
hw_ring_t tx;

ring_handle_t rx_ring;
ring_handle_t tx_ring;

volatile struct eth_mac_regs *eth_mac = (void *)(uintptr_t)0x2000000;
volatile struct eth_dma_regs *eth_dma = (void *)(uintptr_t)0x2000000 + DMA_REG_OFFSET;

static inline bool hw_ring_full(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail + 2 - ring->head) % ring_size);
}

static inline bool hw_ring_empty(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail - ring->head) % ring_size);
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
        while (!hw_ring_full(&rx, RX_COUNT) && !ring_empty(rx_ring.free_ring)) {
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_free(&rx_ring, &buffer);
            assert(!err);

            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (rx.tail + 1 == RX_COUNT) cntl |= DESC_RXCTRL_RXRINGEND;

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, DESC_RXSTS_OWNBYDMA, cntl, buffer.phys_or_offset, 0);
            eth_dma->rxpolldemand = POLL_DATA;

            rx.tail = (rx.tail + 1) % RX_COUNT;
        }

        request_signal(rx_ring.free_ring);
        reprocess = false;

        if (!ring_empty(rx_ring.free_ring) && !hw_ring_full(&rx, RX_COUNT)) {
            cancel_signal(rx_ring.free_ring);
            reprocess = true;
        }
    }
}

static void rx_return(void)
{
    bool packets_transferred = false;
    while (!hw_ring_empty(&rx, RX_COUNT)) {
        /* If buffer slot is still empty, we have processed all packets the device has filled */
        volatile struct descriptor *d = &(rx.descr[rx.head]);
        if (d->status & DESC_RXSTS_OWNBYDMA) break;
        buff_desc_t buffer = rx.descr_mdata[rx.head];
        THREAD_MEMORY_ACQUIRE();

        if (d->status & DESC_RXSTS_ERROR) {
            dprintf("ETH|ERROR: RX descriptor returned with error status %x\n", d->status);
            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (rx.tail + 1 == RX_COUNT) cntl |= DESC_RXCTRL_RXRINGEND;

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, DESC_RXSTS_OWNBYDMA, cntl, buffer.phys_or_offset, 0);
            eth_dma->rxpolldemand = POLL_DATA;
        } else {
            buffer.len = (d->status & DESC_RXSTS_LENMSK) >> DESC_RXSTS_LENSHFT;
            int err __attribute__((unused)) = enqueue_used(&rx_ring, buffer);
            assert(!err);
            packets_transferred = true;
        }
        rx.head = (rx.head + 1) % RX_COUNT;
    }

    if (packets_transferred && require_signal(rx_ring.used_ring)) {
        cancel_signal(rx_ring.used_ring);
        microkit_notify(RX_CH);
    }
}

static void tx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!(hw_ring_full(&tx, TX_COUNT)) && !ring_empty(tx_ring.used_ring)) {
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_used(&tx_ring, &buffer);
            assert(!err);

            uint32_t cntl = (((uint32_t) buffer.len) << DESC_TXCTRL_SIZE1SHFT) & DESC_TXCTRL_SIZE1MASK;
            cntl |= DESC_TXCTRL_TXLAST | DESC_TXCTRL_TXFIRST | DESC_TXCTRL_TXINT;
            if (tx.tail + 1 == TX_COUNT) cntl |= DESC_TXCTRL_TXRINGEND;
            tx.descr_mdata[tx.tail] = buffer;
            update_ring_slot(&tx, tx.tail, DESC_TXSTS_OWNBYDMA, cntl, buffer.phys_or_offset, 0);

            tx.tail = (tx.tail + 1) % TX_COUNT;
        }
    
        request_signal(tx_ring.used_ring);
        reprocess = false;

        if (!hw_ring_full(&tx, TX_COUNT) && !ring_empty(tx_ring.used_ring)) {
            cancel_signal(tx_ring.used_ring);
            reprocess = true;
        }
    }
    eth_dma->txpolldemand = POLL_DATA;
}

static void tx_return(void)
{
    bool enqueued = false;
    while (!hw_ring_empty(&tx, TX_COUNT)) {
        /* Ensure that this buffer has been sent by the device */
        volatile struct descriptor *d = &(tx.descr[tx.head]);
        if (d->status & DESC_TXSTS_OWNBYDMA) break;
        buff_desc_t buffer = tx.descr_mdata[tx.head];
        THREAD_MEMORY_ACQUIRE();

        int err __attribute__((unused)) = enqueue_free(&tx_ring, buffer);
        assert(!err);
        enqueued = true;
        tx.head = (tx.head + 1) % TX_COUNT;
    }

    if (enqueued && require_signal(tx_ring.free_ring)) {
        cancel_signal(tx_ring.free_ring);
        microkit_notify(TX_CH);
    }
}

// size_t dropped;
static void handle_irq()
{
    uint32_t e = eth_dma->status;
    if (e & DMA_INTR_RXF) {
        rx_return();
    }
    if (e & DMA_INTR_TXF) {
        tx_return();
    }
    if (e & DMA_INTR_ABNORMAL) {
        // if (e & DMA_INTR_RBU) {
        //     dropped += eth_dma->missedframecount & MSFRM_MASK;
        //     uint32_t currhostrxdesc = eth_dma->currhostrxdesc;
        //     uint32_t curr_host_index = (currhostrxdesc - hw_ring_buffer_paddr)/sizeof(struct descriptor);
        //     dprintf("Host head: %u, our head %u, our tail %u\n", curr_host_index, rx.head, rx.tail);

        //     rx_provide();
        // }
        if (e & DMA_INTR_FBE) dprintf("Ethernet device fatal bus error\n");
    }
    eth_dma->status &= e;
}

static void eth_setup(void)
{
    uint32_t l = eth_mac->macaddr0lo;
    uint32_t h = eth_mac->macaddr0hi;

    assert((hw_ring_buffer_paddr & 0xFFFFFFFF) == hw_ring_buffer_paddr);

    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
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
    eth_dma->opmode = STOREFORWARD;
    eth_mac->conf = FULLDPLXMODE;

    eth_dma->rxdesclistaddr = hw_ring_buffer_paddr;
    eth_dma->txdesclistaddr = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);

    eth_mac->framefilt |= PMSCUOUS_MODE;
}

void init(void)
{
    eth_setup();

    ring_init(&rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, RX_RING_SIZE_DRIV);
    ring_init(&tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, TX_RING_SIZE_DRIV);

    rx_provide();
    tx_provide();

    /* Enable IRQs */
    eth_dma->intenable |= DMA_INTR_MASK;
    // eth_dma->intenable |= DMA_INTR_RBU;
    
    /* Disable uneeded GMAC irqs */
    eth_mac->intmask |= GMAC_INTR_MASK;

    /* We are ready to receive. Enable. */
    eth_mac->conf |= RX_ENABLE | TX_ENABLE;
    eth_dma->opmode |= TXSTART | RXSTART;

    microkit_irq_ack(IRQ_CH);
}

void notified(microkit_channel ch)
{
    switch(ch) {
        case IRQ_CH:
            handle_irq();
            microkit_irq_ack_delayed(ch);
            break;
        case RX_CH:
            rx_provide();
            break;
        case TX_CH:
            tx_provide();
            break;
        // case IPBENCH_FINISH:
        //     dprintf("Total dropped packets: %llu\n", dropped);
        //     break;
        default:
            dprintf("ETH|LOG: received notification on unexpected channel %llu\n", ch);
            break;
    }
}