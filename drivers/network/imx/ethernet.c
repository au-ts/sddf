/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/serial/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>
#include <serial_config.h>

#include "ethernet.h"

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

uintptr_t eth_regs;
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;

#define SERIAL_TX_CH 3

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;

#define BENCH_FINISH_IN 20

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
    unsigned int tail; /* index to insert at */
    unsigned int head; /* index to remove from */
    net_buff_desc_t descr_mdata[MAX_COUNT]; /* associated meta data array */
    volatile struct descriptor *descr; /* buffer descripter array */
} hw_ring_t;

hw_ring_t rx; /* Rx NIC ring */
hw_ring_t tx; /* Tx NIC ring */

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

#define MAX_PACKET_SIZE     1536

volatile struct enet_regs *eth;

static inline bool hw_ring_full(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail - ring->head + 1) % ring_size);
}

static inline bool hw_ring_empty(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail - ring->head) % ring_size);
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
    __sync_synchronize();
    d->stat = stat;
}

uint64_t rpx_tot = 0;
uint64_t rpx_num = 0;
uint64_t rpx_min = UINT64_MAX;
uint64_t rpx_max = 0;

static void rx_provide(void)
{
    uint64_t rpx_tot_local = 0;
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&rx, RX_COUNT) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint16_t stat = RXD_EMPTY;
            if (rx.tail + 1 == RX_COUNT) {
                stat |= WRAP;
            }
            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, buffer.io_or_offset, 0, stat);
            rx.tail = (rx.tail + 1) % RX_COUNT;
            eth->rdar = RDAR_RDAR;
            rpx_tot_local++;
        }

        /* Only request a notification from virtualiser if HW ring not full */
        if (!hw_ring_full(&rx, RX_COUNT)) {
            net_request_signal_free(&rx_queue);
        } else {
            net_cancel_signal_free(&rx_queue);
        }
        reprocess = false;

        if (!net_queue_empty_free(&rx_queue) && !hw_ring_full(&rx, RX_COUNT)) {
            net_cancel_signal_free(&rx_queue);
            reprocess = true;
        }
    }

    rpx_num++;
    rpx_tot += rpx_tot_local;
    if (rpx_tot_local > rpx_max) rpx_max = rpx_tot_local;
    if (rpx_tot_local < rpx_min) rpx_min = rpx_tot_local;
}

uint64_t rrx_tot = 0;
uint64_t rrx_num = 0;
uint64_t rrx_min = UINT64_MAX;
uint64_t rrx_max = 0;

static void rx_return(void)
{
    uint64_t rrx_tot_local = 0;
    bool packets_transferred = false;
    while (!hw_ring_empty(&rx, RX_COUNT)) {
        /* If buffer slot is still empty, we have processed all packets the device has filled */
        volatile struct descriptor *d = &(rx.descr[rx.head]);
        if (d->stat & RXD_EMPTY) {
            break;
        }

        net_buff_desc_t buffer = rx.descr_mdata[rx.head];
        buffer.len = d->len;
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        packets_transferred = true;
        rx.head = (rx.head + 1) % RX_COUNT;
        rrx_tot_local++;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(RX_CH);
    }

    rrx_num++;
    rrx_tot += rrx_tot_local;
    if (rrx_tot_local > rrx_max) rrx_max = rrx_tot_local;
    if (rrx_tot_local < rrx_min) rrx_min = rrx_tot_local;
}

uint64_t tpx_tot = 0;
uint64_t tpx_num = 0;
uint64_t tpx_min = UINT64_MAX;
uint64_t tpx_max = 0;

static void tx_provide(void)
{
    uint64_t tpx_tot_local = 0;
    bool reprocess = true;
    while (reprocess) {
        while (!(hw_ring_full(&tx, TX_COUNT)) && !net_queue_empty_active(&tx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            uint16_t stat = TXD_READY | TXD_ADDCRC | TXD_LAST;
            if (tx.tail + 1 == TX_COUNT) {
                stat |= WRAP;
            }
            tx.descr_mdata[tx.tail] = buffer;
            update_ring_slot(&tx, tx.tail, buffer.io_or_offset, buffer.len, stat);

            tx.tail = (tx.tail + 1) % TX_COUNT;
            eth->tdar = TDAR_TDAR;
            tpx_tot_local++;
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_ring_full(&tx, TX_COUNT) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }

    tpx_num++;
    tpx_tot += tpx_tot_local;
    if (tpx_tot_local > tpx_max) tpx_max = tpx_tot_local;
    if (tpx_tot_local < tpx_min) tpx_min = tpx_tot_local; 
}

uint64_t trx_tot = 0;
uint64_t trx_num = 0;
uint64_t trx_min = UINT64_MAX;
uint64_t trx_max = 0;

static void tx_return(void)
{
    uint64_t trx_tot_local = 0;
    bool enqueued = false;
    while (!hw_ring_empty(&tx, TX_COUNT)) {
        /* Ensure that this buffer has been sent by the device */
        volatile struct descriptor *d = &(tx.descr[tx.head]);
        if (d->stat & TXD_READY) {
            break;
        }

        net_buff_desc_t buffer = tx.descr_mdata[tx.head];
        buffer.len = 0;

        tx.head = (tx.head + 1) % TX_COUNT;

        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);
        enqueued = true;
        trx_tot_local++;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(TX_CH);
    }

    trx_num++;
    trx_tot += trx_tot_local;
    if (trx_tot_local > trx_max) trx_max = trx_tot_local;
    if (trx_tot_local < trx_min) trx_min = trx_tot_local; 
}

static void handle_irq(void)
{
    uint32_t e = eth->eir & IRQ_MASK;
    eth->eir = e;

    while (e & IRQ_MASK) {
        if (e & NETIRQ_TXF) {
            tx_return();
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
    eth = (struct enet_regs *)eth_regs;
    uint32_t l = eth->palr;
    uint32_t h = eth->paur;

    /* Set up HW rings */
    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
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
    /* clear rx store and forward. This must be done for hardware csums*/
    eth->rsfl = 0;
    /* Do not forward frames with errors + check the csum */
    eth->racc = RACC_LINEDIS | RACC_IPDIS | RACC_PRODIS;
    /* Add the checksum for known IP protocols */
    eth->tacc = TACC_PROCHK | TACC_IPCHK;

    /* Set RDSR */
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
    serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue, serial_tx_data);
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);

    eth_setup();

    net_queue_init(&rx_queue, (net_queue_t *)rx_free, (net_queue_t *)rx_active, NET_RX_QUEUE_SIZE_DRIV);
    net_queue_init(&tx_queue, (net_queue_t *)tx_free, (net_queue_t *)tx_active, NET_TX_QUEUE_SIZE_DRIV);

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
        microkit_irq_ack_delayed(ch);
        break;
    case RX_CH:
        rx_provide();
        break;
    case TX_CH:
        tx_provide();
        break;
    case BENCH_FINISH_IN:
        sddf_printf("ETH Rx Return Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", rrx_tot/rrx_num, rrx_min, rrx_max);
        sddf_printf("ETH Rx Provide Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", rpx_tot/rpx_num, rpx_min, rpx_max);
        sddf_printf("ETH Tx Return Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", trx_tot/trx_num, trx_min, trx_max);
        sddf_printf("ETH Tx Provide Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", tpx_tot/tpx_num, tpx_min, tpx_max);
        rrx_tot = 0;
        rrx_num = 0;
        rrx_min = UINT64_MAX;
        rrx_max = 0;
        rpx_tot = 0;
        rpx_num = 0;
        rpx_min = UINT64_MAX;
        rpx_max = 0;
        trx_tot = 0;
        trx_num = 0;
        trx_min = UINT64_MAX;
        trx_max = 0;
        tpx_tot = 0;
        tpx_num = 0;
        tpx_min = UINT64_MAX;
        tpx_max = 0;
        break;
    default:
        sddf_dprintf("ETH|LOG: received notification on unexpected channel: %u\n", ch);
        break;
    }
}