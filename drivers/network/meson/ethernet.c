/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sel4/sel4.h>
#include <sddf/network/shared_ringbuffer.h>
#include "ethernet.h"

#define IRQ_2  0
#define IRQ_CH 1
#define TX_CH  2
#define RX_CH  2
#define INIT   4

/* Memory regions. These all have to be here to keep compiler happy */
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;
uintptr_t shared_dma_vaddr;
uintptr_t shared_dma_paddr;
uintptr_t rx_cookies;
uintptr_t tx_cookies;
uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;

/* Make the minimum frame buffer 2k. This is a bit of a waste of memory, but ensures alignment */
#define PACKET_BUFFER_SIZE  2048
#define MAX_PACKET_SIZE     1536

#define RX_COUNT 256
#define TX_COUNT 256

_Static_assert((512 * 2) * PACKET_BUFFER_SIZE <= 0x200000, "Expect rx+tx buffers to fit in single 2MB page");
_Static_assert(sizeof(ring_buffer_t) <= 0x200000, "Expect ring buffer ring to fit in single 2MB page");

struct descriptor {
    uint32_t status;
    uint32_t cntl;
    uint32_t addr;
    uint32_t next;
};

typedef struct {
    unsigned int cnt;
    unsigned int remain;
    unsigned int tail;
    unsigned int head;
    volatile struct descriptor *descr;
    uintptr_t phys;
    void **cookies;
} ring_ctx_t;

ring_ctx_t rx;
ring_ctx_t tx;
unsigned int tx_lengths[TX_COUNT];

/* Pointers to shared_ringbuffers */
ring_handle_t rx_ring;
ring_handle_t tx_ring;

static uint8_t mac[6];

volatile struct eth_mac_regs *eth_mac = (void *)(uintptr_t)0x2000000;
volatile struct eth_dma_regs *eth_dma = (void *)(uintptr_t)0x2000000 + DW_DMA_BASE_OFFSET;

static void get_mac_addr(volatile struct eth_mac_regs *reg, uint8_t *mac)
{
    uint32_t l, h;
    l = reg->macaddr0lo;
    h = reg->macaddr0hi;

    mac[3] = l >> 24;
    mac[2] = l >> 16 & 0xff;
    mac[1] = l >> 8 & 0xff;
    mac[0] = l & 0xff;
    mac[5] = h >> 8 & 0xff;
    mac[4] = h & 0xff;
}

static void set_mac(volatile struct eth_mac_regs *reg, uint8_t *mac)
{
    reg->macaddr0lo = mac[0] + (mac[1] << 8) + (mac[2] << 16) +
               (mac[3] << 24);
    reg->macaddr0hi = mac[4] + (mac[5] << 8);
}

static void
dump_mac(uint8_t *mac)
{
    for (unsigned i = 0; i < 6; i++) {
        //printf("%c%c", hexchar((mac[i] >> 4) & 0xf), hexchar(mac[i] & 0xf));
        if (i < 5) {
            //printf(":");
        }
    }
}

static uintptr_t 
getPhysAddr(uintptr_t virtual)
{
    uint64_t offset = virtual - shared_dma_vaddr;
    uintptr_t phys;

    if (offset < 0) {
        //printf("getPhysAddr: offset < 0\n");
        return 0;
    }

    phys = shared_dma_paddr + offset;
    return phys;
}

static void update_ring_slot(
    ring_ctx_t *ring,
    unsigned int idx,
    uint32_t status,
    uint32_t cntl,
    uint32_t phys)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->addr = phys;
    d->cntl = cntl;
    d->status = status;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    __sync_synchronize();
}

static uintptr_t 
alloc_rx_buf(size_t buf_size, void **cookie)
{
    uintptr_t addr;
    unsigned int len;

    /* Try to grab a buffer from the available ring */
    if (driver_dequeue(rx_ring.free_ring, &addr, &len, cookie)) {
        //printf("RX Available ring is empty\n");
        return 0;
    }

    return getPhysAddr(addr);
}

static void fill_rx_bufs()
{
    ring_ctx_t *ring = &rx;
    __sync_synchronize();
    while (ring->remain > 0) {
        /* request a buffer */
        void *cookie = NULL;
        uintptr_t phys = alloc_rx_buf(MAX_PACKET_SIZE, &cookie);
        if (!phys) {
            break;
        }
        uint32_t status = DESC_RXSTS_OWNBYDMA;
        uint32_t cntl = (MAC_MAX_FRAME_SZ & DESC_RXCTRL_SIZE1MASK) | DESC_RXCTRL_RXCHAIN;

        int idx = ring->tail;
        int new_tail = idx + 1;
        if (new_tail == ring->cnt) {
            new_tail = 0;
        }
        ring->cookies[idx] = cookie;
        update_ring_slot(ring, idx, status, cntl, phys);
        ring->tail = new_tail;
        /* There is a race condition if add/remove is not synchronized. */
        ring->remain--;
    }
    __sync_synchronize();

    if (ring->tail != ring->head) {
        /* Make sure rx is enabled */
        eth_mac->conf |= RXENABLE;
    }

    eth_dma->rxpolldemand = POLL_DATA;
}

static void
handle_rx()
{
    ring_ctx_t *ring = &rx;
    unsigned int head = ring->head;

    int num = 1;
    int was_empty = ring_empty(rx_ring.used_ring);

    // we don't want to dequeue packets if we have nothing to replace it with
    while (head != ring->tail && (ring_size(rx_ring.free_ring) > num)) {
        volatile struct descriptor *d = &(ring->descr[head]);
        unsigned int status = d->status;
        /* Ensure no memory references get ordered before we checked the descriptor was written back */
        __sync_synchronize();
        /* If the slot is still marked as ready we are done. */
        if (status & DESC_RXSTS_OWNBYDMA) {
            break;
        }

        unsigned int len = (status & DESC_RXSTS_FRMLENMSK) >> DESC_RXSTS_FRMLENSHFT;

        void *cookie = ring->cookies[head];
        /* Go to next buffer, handle roll-over. */
        if (++head == ring->cnt) {
            head = 0;
        }
        ring->head = head;

        /* There is a race condition here if add/remove is not synchronized. */
        ring->remain++;

        buff_desc_t *desc = (buff_desc_t *)cookie;

        enqueue_used(&rx_ring, desc->encoded_addr, len, desc->cookie);
        num++;
    }

    /* Notify client (only if we have actually processed a packet and 
    the client hasn't already been notified!) */
    if (num > 1 && was_empty) {
        microkit_notify(RX_CH);
    } 
}

static void
complete_tx()
{
    unsigned int cnt_org;
    void *cookie;
    ring_ctx_t *ring = &tx;
    unsigned int head = ring->head;
    unsigned int cnt = 0;


    while (head != ring->tail) {
        if (0 == cnt) {
            cnt = tx_lengths[head];
            if ((0 == cnt) || (cnt > TX_COUNT)) {
                /* We are not supposed to read 0 here. */
                //printf("complete_tx with cnt=0 or max\n");
                return;
            }
            cnt_org = cnt;
            cookie = ring->cookies[head];
        }

        volatile struct descriptor *d = &(ring->descr[head]);

        /* If this buffer was not sent, we can't release any buffer. */
        if (d->status & DESC_TXSTS_OWNBYDMA) {
            /* not complete yet */
            // //printf("Buffer was not sent\n");
            return;
        }

        /* Go to next buffer, handle roll-over. */
        if (++head == TX_COUNT) {
            head = 0;
        }

        if (0 == --cnt) {
            ring->head = head;
            /* race condition if add/remove is not synchronized. */
            ring->remain += cnt_org;
            /* give the buffer back */
            buff_desc_t *desc = (buff_desc_t *)cookie;

            enqueue_free(&tx_ring, desc->encoded_addr, desc->len, desc->cookie);
        }
    }

    /* The only reason to arrive here is when head equals tails. If cnt is not
     * zero, then there is some kind of overflow or data corruption. The number
     * of tx descriptors holding data can't exceed the space in the ring.
     */
    if (0 != cnt) {
        //printf("head reached tail, but cnt!= 0\n");
    }
}

static void
raw_tx(unsigned int num, uintptr_t *phys, unsigned int *len, void *cookie)
{
    ring_ctx_t *ring = &tx;

    /* Ensure we have room */
    if (ring->remain < num) {
        /* not enough room, try to complete some and check again */
        complete_tx();
        unsigned int rem = ring->remain;
        if (rem < num) {
            //printf("TX queue lacks space\n");
            return;
        }
    }

    __sync_synchronize();

    unsigned int tail = ring->tail;
    unsigned int tail_new = tail;

    unsigned int i = num;
    while (i-- > 0) {
        uint32_t cntl = DESC_TXCTRL_TXCHAIN;
        cntl |= ((*len++) << DESC_TXCTRL_SIZE1SHFT) & DESC_TXCTRL_SIZE1MASK;
        cntl |= DESC_TXCTRL_TXLAST | DESC_TXCTRL_TXFIRST;
        cntl |= DESC_TXCTRL_TXINT;

        unsigned int idx = tail_new;
        if (++tail_new == TX_COUNT) {
            tail_new = 0;
        }
        if (ring->descr[idx].status & DESC_TXSTS_OWNBYDMA) {
            //printf("CPU not owner of frame!\n");
        }
        update_ring_slot(ring, idx, DESC_TXSTS_OWNBYDMA, cntl, *phys++);
    }

    ring->cookies[tail] = cookie;
    tx_lengths[tail] = num;
    ring->tail = tail_new;
    /* There is a race condition here if add/remove is not synchronized. */
    ring->remain -= num;

    __sync_synchronize();

    if (!(eth_mac->conf & TXENABLE)) {
        eth_mac->conf |= TXENABLE;
    }

    /* Start the transmission */
	eth_dma->txpolldemand = POLL_DATA;
}

static void 
handle_eth(volatile struct eth_dma_regs *eth_dma)
{
    uint32_t e = eth_dma->status;
    /* write to clear events */
    eth_dma->status = e;

    while (e & DMA_INTR_DEFAULT_MASK) {
        if (e & DMA_INTR_ENA_TIE) {
            complete_tx();
        }
        if (e & DMA_INTR_ENA_RIE) {
            handle_rx();
            fill_rx_bufs();
        }
        if (e & DMA_INTR_ABNORMAL) {
            //printf("Error: System bus/uDMA: %llx\n", e);
            if (e & DMA_INTR_ENA_FBE) {
                //printf("    Ethernet device fatal bus error\n");
            }
            if (e & DMA_INTR_ENA_UNE) {
                //printf("    Ethernet device TX underflow\n");
            }
            if (e & DMA_INTR_ENA_RBU) {
                //printf("    Ethernet device RX Buffer unavailable\n");
            }
            if (e & DMA_INTR_ENA_RPS) {
                //printf("    Ethernet device RX Stopped\n");
                fill_rx_bufs();
                break;
            }
            while (1);
        }
        e = eth_dma->status;
        eth_dma->status = e;
    }
}

static void 
handle_tx()
{
    uintptr_t buffer = 0;
    unsigned int len = 0;
    void *cookie = NULL;

    // We need to put in an empty condition here. 
    while ((tx.remain > 1) && !driver_dequeue(tx_ring.used_ring, &buffer, &len, &cookie)) {
        uintptr_t phys = getPhysAddr(buffer);
        raw_tx(1, &phys, &len, cookie);
    }
}

static void 
eth_setup(void)
{
    get_mac_addr(eth_mac, mac);
    //printf("MAC: ");
    dump_mac(mac);
    //printf("\n");

    /* set up descriptor rings */
    rx.cnt = RX_COUNT;
    rx.remain = rx.cnt - 2;
    rx.tail = 0;
    rx.head = 0;
    rx.phys = shared_dma_paddr;
    rx.cookies = (void **)rx_cookies;
    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;

    uintptr_t next_phys = hw_ring_buffer_paddr;
    // TODO: Set the descriptor->next field to be the next one. 
    for (unsigned int i = 0; i < rx.cnt; i++) {
        next_phys += sizeof(struct descriptor);
        if (i == (rx.cnt - 1)) {
            rx.descr[i].next = (uint32_t)(hw_ring_buffer_paddr & 0xFFFFFFFF);
        } else {
            rx.descr[i].next = (uint32_t)(next_phys & 0xFFFFFFFF);
        }
        rx.descr[i].status = 0;
        rx.descr[i].addr = 0;
        rx.descr[i].cntl = (MAC_MAX_FRAME_SZ & DESC_RXCTRL_SIZE1MASK) | DESC_RXCTRL_RXCHAIN;
    }

    tx.cnt = TX_COUNT;
    tx.remain = tx.cnt - 2;
    tx.tail = 0;
    tx.head = 0;
    tx.phys = shared_dma_paddr + (sizeof(struct descriptor) * RX_COUNT);
    tx.cookies = (void **)tx_cookies;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

    next_phys = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);
    for (unsigned int i = 0; i < tx.cnt; i++) {
        next_phys += sizeof(struct descriptor);
        if (i == (tx.cnt - 1)) {
            tx.descr[i].next = (uint32_t)((hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT)) & 0xFFFFFFFF);
        } else {
            tx.descr[i].next = (uint32_t)(next_phys & 0xFFFFFFFF);
        }
        tx.descr[i].status = 0;
        tx.descr[i].cntl = DESC_TXCTRL_TXCHAIN;
        tx.descr[i].addr = 0;
    }

    /* Perform reset */
    eth_dma->busmode |= DMAMAC_SRST;
    while (eth_dma->busmode & DMAMAC_SRST);

    /* Reset removes the mac address */
    set_mac(eth_mac, mac);

    eth_dma->busmode |= FIXEDBURST | PRIORXTX_41 | DMA_PBL;
    eth_dma->opmode |= FLUSHTXFIFO | STOREFORWARD;

    eth_mac->conf |= FRAMEBURSTENABLE | DISABLERXOWN | FULLDPLXMODE;

    eth_dma->rxdesclistaddr = hw_ring_buffer_paddr;
    eth_dma->txdesclistaddr = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);
}

void init_post()
{
    /* Set up shared memory regions */
    ring_init(&rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, 0, SIZE, SIZE);
    ring_init(&tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, 0, SIZE, SIZE);

    fill_rx_bufs();

    /* Enable IRQs */
    eth_dma->intenable |= DMA_INTR_DEFAULT_MASK;
    /* Disable uneeded GMAC irqs */
    eth_mac->intmask |= GMAC_INT_DEFAULT_MASK;

    /* We are ready to receive. Enable. */
    eth_mac->conf |= RXENABLE | TXENABLE;
    eth_dma->opmode |= TXSTART | RXSTART;

    //printf("%s: init complete -- waiting for interrupt\n", microkit_name);
    microkit_notify(INIT);

    /* Now take away our scheduling context. Uncomment this for a passive driver. */
    /* have_signal = true;
    msg = seL4_MessageInfo_new(0, 0, 0, 1);
    seL4_SetMR(0, 0);
    signal = (MONITOR_EP); */
    microkit_irq_ack(IRQ_CH);
}

void init(void)
{
    //printf("%s: elf PD init function running\n", microkit_name);
    microkit_dbg_puts("ethernet init!\n");

    eth_setup();

    /* Now wait for notification from lwip that buffers are initialised */
}

seL4_MessageInfo_t
protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (ch) {
        case INIT:
            // return the MAC address. 
            microkit_mr_set(0, eth_mac->macaddr0lo);
            microkit_mr_set(1, eth_mac->macaddr0hi);
            return microkit_msginfo_new(0, 2);
        case TX_CH:
            handle_tx();
            break;
        default:
            //printf("Received ppc on unexpected channel %d\n", ch);
            break;
    }
    return microkit_msginfo_new(0, 0);
}

void notified(microkit_channel ch)
{
    switch(ch) {
        case IRQ_CH:
            handle_eth(eth_dma);
            have_signal = true;
            signal_msg = seL4_MessageInfo_new(IRQAckIRQ, 0, 0, 0);
            signal = (BASE_IRQ_CAP + IRQ_CH);
            return;
        case IRQ_2:
            handle_eth(eth_dma);
            have_signal = true;
            signal_msg = seL4_MessageInfo_new(IRQAckIRQ, 0, 0, 0);
            signal = (BASE_IRQ_CAP + IRQ_CH);
        case INIT:
            init_post();
            break;
        case TX_CH:
            handle_tx();
            break;
        default:
            //printf("eth driver: received notification on unexpected channel %d\n", ch);
            break;
    }
}
