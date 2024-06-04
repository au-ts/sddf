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
} descriptor_t;

volatile struct descriptor * rx_desc;
volatile struct descriptor * tx_desc;

/* HW ring buffer data type */
typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    volatile struct descriptor *descr; /* buffer descriptor array */
    uint64_t descr_mdata[MAX_COUNT]; /* associated meta data array */
} hw_ring_t;

hw_ring_t rx; /* Rx NIC ring */
hw_ring_t tx; /* Tx NIC ring */

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

#define MAX_PACKET_SIZE     1536

volatile struct enet_regs *eth;

#define RXD_STAT        0x8000   
#define RXD_STAT_WRAP   0xa000
static inline void rx_update_ring_slot(uint64_t idx, net_buff_desc_t* buffer)
{
    volatile struct descriptor *dst_addr = &(rx_desc[idx]);
    uint16_t stat = RXD_STAT;
    if (idx + 1 == RX_COUNT) {
        stat = RXD_STAT_WRAP;
    }
    dst_addr->addr = buffer->io_or_offset;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    __sync_synchronize();
    dst_addr->stat = stat;
}

#define TX_STAT         0x8c00
#define TX_STAT_WRAP    0xac00
static inline void tx_update_ring_slot(uint64_t idx, net_buff_desc_t* buffer)
{
    volatile struct descriptor *dst_addr = &(tx_desc[idx]);
    uint16_t stat = TX_STAT;
    if (idx + 1 == TX_COUNT) {
        stat = TX_STAT_WRAP;
    }
    dst_addr->addr = buffer->io_or_offset;
    dst_addr->len = buffer->len;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    __sync_synchronize();
    dst_addr->stat = stat;
}

static inline bool rx_hw_queue_empty() 
{
    return rx.head == rx.tail;
}

static inline bool tx_hw_queue_empty() 
{
    return tx.head == tx.tail;
}

static inline bool rx_hw_queue_full() 
{
    uint64_t new_tail = (rx.tail + 1) % RX_COUNT;
    return new_tail == rx.head;
}

static inline bool tx_hw_queue_full() 
{
    uint64_t new_tail = (tx.tail + 1) % TX_COUNT;
    return new_tail == tx.head;
}

static inline void hw_ring_rx_enqueue(net_buff_desc_t* buffer) 
{
    uint64_t idx = rx.tail;
    rx.descr_mdata[idx] = buffer->io_or_offset;
    rx_update_ring_slot(idx, buffer);
    rx.tail = (idx + 1) % RX_COUNT;
}

static inline void hw_ring_tx_enqueue(net_buff_desc_t* buffer) 
{
    uint64_t idx = tx.tail;
    tx.descr_mdata[idx] = buffer->io_or_offset;
    tx_update_ring_slot(idx, buffer);
    tx.tail = (idx + 1) % TX_COUNT;
}

static inline net_buff_desc_t hw_ring_rx_dequeue()
{
    uint64_t idx = rx.head;
    volatile struct descriptor *dst_addr = &(rx_desc[idx]);
    net_buff_desc_t buffer;
    buffer.io_or_offset = rx.descr_mdata[idx];
    buffer.len = dst_addr->len;
    rx.head = (idx + 1) % RX_COUNT;
    return buffer;
}

static inline net_buff_desc_t hw_ring_tx_dequeue()
{
    uint64_t idx = tx.head;
    net_buff_desc_t buffer;
    buffer.io_or_offset = tx.descr_mdata[idx];
    buffer.len = 0;
    tx.head = (idx + 1) % TX_COUNT;
    return buffer;
}

static void rx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!rx_hw_queue_full() && !net_queue_empty(rx_free)) {
            net_buff_desc_t* buffer = net_dequeue(rx_free, NET_RX_QUEUE_CAPACITY_DRIV);
            hw_ring_rx_enqueue(buffer);
            eth->rdar = RDAR_RDAR;
        }

        /* Only request a notification from virtualiser if HW ring not full */
        bool full = rx_hw_queue_full();
        if (!full) {
            net_request_signal(rx_free);
        } else {
            net_cancel_signal(rx_free);
        }
        reprocess = false;

        if (!net_queue_empty(rx_free) && !full) {
            net_cancel_signal(rx_free);
            reprocess = true;
        }
    }
}

static void rx_return(void)
{
    bool packets_transferred = false;
    while (!rx_hw_queue_empty() && !net_queue_full(rx_active, NET_RX_QUEUE_CAPACITY_DRIV)) {
        /* If buffer slot is still empty, we have processed all packets the device has filled */
        volatile struct descriptor *d = &(rx_desc[rx.head]);
        if (d->stat & RXD_EMPTY) {
            break;
        }
        net_buff_desc_t buffer = hw_ring_rx_dequeue();
        net_enqueue(rx_active, buffer, NET_RX_QUEUE_CAPACITY_DRIV);
        packets_transferred = true;
    }

    if (packets_transferred && net_require_signal(rx_active)) {
        net_cancel_signal(rx_active);
        microkit_notify(RX_CH);
    }
}

static void tx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!tx_hw_queue_full() && !net_queue_empty(tx_active)) 
        {
            net_buff_desc_t* buffer = net_dequeue(tx_active, NET_TX_QUEUE_CAPACITY_DRIV);
            hw_ring_tx_enqueue(buffer);
            eth->tdar = TDAR_TDAR;
        }

        net_request_signal(tx_active);
        reprocess = false;

        if (!tx_hw_queue_full() && !net_queue_empty(tx_active)) {
            net_cancel_signal(tx_active);
            reprocess = true;
        }
    }
}

static void tx_return(void)
{
    bool enqueued = false;
    while (!tx_hw_queue_empty() && !net_queue_full(tx_free, NET_TX_QUEUE_CAPACITY_DRIV)) 
    {
        /* Ensure that this buffer has been sent by the device */
        volatile struct descriptor *d = &(tx_desc[tx.head]);
        if (d->stat & TXD_READY) {
            break;
        }
        net_buff_desc_t buffer = hw_ring_tx_dequeue();
        net_enqueue(tx_free, buffer, NET_TX_QUEUE_CAPACITY_DRIV);
        enqueued = true;
    }

    if (enqueued && net_require_signal(tx_free)) {
        net_cancel_signal(tx_free);
        microkit_notify(TX_CH);
    }
}

#define IRQ_MASK_       0xa000000
#define NETIRQ_TXF_     0x8000000
#define NETIRQ_RXF_     0x2000000
static void handle_irq(void)
{
    uint32_t e = eth->eir & IRQ_MASK;
    eth->eir = e;

    while (e & IRQ_MASK_) {
        if (e & NETIRQ_TXF_) {
            tx_return();
            tx_provide();
        }
        if (e & NETIRQ_RXF_) {
            rx_return();
            rx_provide();
        }
        e = eth->eir & IRQ_MASK_;
        eth->eir = e;
    }
}

static void eth_setup(void)
{
    uint32_t l = eth->palr;
    uint32_t h = eth->paur;

    /* Set up HW rings */
    rx_desc = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx_desc = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

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
    eth->eimr = IRQ_MASK_;
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
