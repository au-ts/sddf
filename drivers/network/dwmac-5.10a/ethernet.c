/*
 * Copyright 2024, UNSW
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
#include <sddf/network/util.h>

#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

uintptr_t eth_regs;
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;
uintptr_t rx_desc_base;
uintptr_t tx_desc_base;
uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;

#ifdef CONFIG_PLAT_STAR64
uintptr_t resets;
#endif /* CONFIG_PLAT_STAR64 */

#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

struct descriptor {
    uint32_t d0;
    uint32_t d1;
    uint32_t d2;
    uint32_t d3;
};

_Static_assert((RX_COUNT + TX_COUNT) * sizeof(struct descriptor) <= NET_HW_REGION_SIZE,
               "Expect rx+tx buffers to fit in single 2MB page");

typedef struct {
    unsigned int tail; /* index to insert at */
    unsigned int head; /* index to remove from */
    net_buff_desc_t descr_mdata[MAX_COUNT]; /* associated meta data array */
    volatile struct descriptor *descr; /* buffer descripter array. This is what lives in the hardware_ring address. */
} hw_ring_t;

hw_ring_t rx;
hw_ring_t tx;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

#define MAC_REG(x) ((volatile uint32_t *)(eth_regs + x))
#define MTL_REG(x) ((volatile uint32_t *)(eth_regs + x))
#define DMA_REG(x) ((volatile uint32_t *)(eth_regs + x))
#define writel(b, addr) (void)((*(volatile uint32_t *)(addr)) = (b))
#define readl(addr) \
	({ unsigned int __v = (*(volatile uint32_t *)(addr)); __v; })

static inline bool hw_ring_full(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail + 1 - ring->head) % ring_size);
}

static inline bool hw_ring_empty(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail - ring->head) % ring_size);
}

static void update_ring_slot(hw_ring_t *ring, unsigned int idx, uint32_t d0, uint32_t d1,
                            uint32_t d2, uint32_t d3)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->d0 = d0;
    d->d1 = d1;
    d->d2 = d2;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    THREAD_MEMORY_RELEASE();
    d->d3 = d3;
}

size_t free_dequeued = 0;

static void rx_provide()
{
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&rx, RX_COUNT) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);
            free_dequeued += 1;

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, (uint32_t) (buffer.io_or_offset & 0xffffffff),
                            (uint32_t) (buffer.io_or_offset >> 32), 0, (uint32_t) (DESC_RXSTS_OWNBYDMA | DESC_RXSTS_BUFFER1_ADDR_VALID | DESC_RXSTS_IOC));
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            THREAD_MEMORY_RELEASE();
            *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + sizeof(struct descriptor) * rx.tail;
            rx.tail = (rx.tail + 1) % RX_COUNT;
        }

        net_request_signal_free(&rx_queue);
        reprocess = false;


        if (!net_queue_empty_free(&rx_queue) && !hw_ring_full(&rx, RX_COUNT)) {
            net_cancel_signal_free(&rx_queue);
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
        if (d->d3 & DESC_RXSTS_OWNBYDMA) {
            break;
        }
        net_buff_desc_t buffer = rx.descr_mdata[rx.head];
        THREAD_MEMORY_ACQUIRE();

        if (d->d3 & DESC_RXSTS_ERROR) {
            sddf_dprintf("ETH|ERROR: RX descriptor returned with error status %x\n", d->d3);

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, (uint32_t) (buffer.io_or_offset & 0xffffffff),
                            (uint32_t) (buffer.io_or_offset >> 32), 0, (uint32_t) (DESC_RXSTS_OWNBYDMA | DESC_RXSTS_BUFFER1_ADDR_VALID | DESC_RXSTS_IOC));

            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + sizeof(struct descriptor) * rx.tail;
            rx.head = (rx.head + 1) % RX_COUNT;
        } else {
            buffer.len = (d->d3 | 0xe);
            int err = net_enqueue_active(&rx_queue, buffer);
            assert(!err);
            packets_transferred = true;
            rx.head = (rx.head + 1) % RX_COUNT;
        }
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(RX_CH);
    }
}

static void tx_provide(void)
{
    bool reprocess = true;
    int i = 0;
    while (reprocess) {
        while (!(hw_ring_full(&tx, TX_COUNT)) && !net_queue_empty_active(&tx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            // For normal transmit descriptors, tdes2 needs to be set to generate an IRQ on transmit
            // completion. We also need to provide the length of the buffer data in bits 13:0.
            uint32_t tdes2 = DESC_TXCTRL_TXINT | buffer.len;

            // For normal transmit descritpors, we need to give ownership to DMA, as well as indicate
            // that this is the first and last parts of the current packet.
            uint32_t tdes3 = (DESC_TXSTS_OWNBYDMA | DESC_TXCTRL_TXFIRST | DESC_TXCTRL_TXLAST | DESC_TXCTRL_TXCIC |buffer.len);
            tx.descr_mdata[tx.tail] = buffer;

            update_ring_slot(&tx, tx.tail, buffer.io_or_offset & 0xffffffff, buffer.io_or_offset >> 32, tdes2, tdes3);

            tx.tail = (tx.tail + 1) % TX_COUNT;
            i++;
            /* Set the tail in hardware to the latest tail we have inserted in.
             * This tells the hardware that it has new buffers to send.
             * NOTE: Setting this on every enqueued packet for sanity, change this to once per bactch.
             */
            *DMA_REG(DMA_CHAN_TX_TAIL_ADDR(0)) = tx_desc_base + sizeof(struct descriptor) * (tx.tail);
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_ring_full(&tx, TX_COUNT) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }

}

static void tx_return(void)
{
    bool enqueued = false;
    while (!hw_ring_empty(&tx, TX_COUNT)) {
        /* Ensure that this buffer has been sent by the device */
        volatile struct descriptor *d = &(tx.descr[tx.head]);
        if (d->d3 & DESC_TXSTS_OWNBYDMA) {
            break;
        }
        net_buff_desc_t buffer = tx.descr_mdata[tx.head];
        THREAD_MEMORY_ACQUIRE();

        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);
        enqueued = true;
        tx.head = (tx.head + 1) % TX_COUNT;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(TX_CH);
    }
}

static void handle_irq()
{
    uint32_t e = *DMA_REG(DMA_CHAN_STATUS(0));
    if (e & DMA_CHAN_INTR_ENA_RIE) {
        rx_return();
    }
    if (e & DMA_CHAN_INTR_ENA_TIE) {
        tx_return();
    }
    if (e & DMA_CHAN_INTR_ABNORMAL) {
        if (e & DMA_CHAN_INTR_ENA_FBE) {
            sddf_dprintf("Ethernet device fatal bus error\n");
        }
    }
    *DMA_REG(DMA_CHAN_STATUS(0)) &= e;
}

static void eth_init()
{
    // Software reset -- This will reset the MAC internal registers.
    volatile uint32_t *mode = DMA_REG(DMA_BUS_MODE);
    *mode |= DMA_BUS_MODE_SFT_RESET;

    // Poll on BIT 0. This bit is cleared by the device when the reset is complete.
    while(1) {
        mode = DMA_REG(DMA_BUS_MODE);
        if (!(*mode & DMA_BUS_MODE_SFT_RESET)) {
            break;
        }
    }

    /* Configure MTL */

    // Enable store and forward mode for TX, and enable the TX queue.
    *MTL_REG(MTL_CHAN_TX_OP_MODE(0)) |= MTL_OP_MODE_TSF | MTL_OP_MODE_TXQ_ENABLE;

    // Enable store and forward mode for rx
    *MTL_REG(MTL_CHAN_RX_OP_MODE(0)) |= MTL_OP_MODE_RSF;

    // Program the rx queue to the DMA mapping.
    uint32_t map0 = *MTL_REG(MTL_RXQ_DMA_MAP0);
    // We only have one queue, and we map it onto DMA channel 0
    map0 &= ~MTL_RXQ_DMA_QXMDMACH_MASK(0);
    map0 |= MTL_RXQ_DMA_QXMDMACH(0, 0);
    *MTL_REG(MTL_RXQ_DMA_MAP0) = map0;


    // Transmit/receive queue fifo size, use all RAM for 1 queue
    uint32_t val = *MAC_REG(GMAC_HW_FEATURE1);
    uint32_t tx_fifo_sz;
    uint32_t rx_fifo_sz;
    // These sizes of the tx and rx FIFO are encoded in the hardware feature 1 register.
    // These values are expressed as: Log2(FIFO_SIZE) -7
    tx_fifo_sz = (val >> 6) & 0x1f;
    rx_fifo_sz = (val >> 0) & 0x1f;

    /* r/tx_fifo_sz is encoded as log2(n / 128). Undo that by shifting */
    tx_fifo_sz = 128 << tx_fifo_sz;
    rx_fifo_sz = 128 << rx_fifo_sz;

    /* r/tqs is encoded as (n / 256) - 1 */
    uint32_t tqs = tx_fifo_sz / 256 - 1;
    uint32_t rqs = rx_fifo_sz / 256 - 1;

    *MTL_REG(MTL_CHAN_TX_OP_MODE(0)) &= ~(MTL_OP_MODE_TQS_MASK);
    *MTL_REG(MTL_CHAN_TX_OP_MODE(0)) |= tqs << MTL_OP_MODE_TQS_SHIFT;
    *MTL_REG(MTL_CHAN_RX_OP_MODE(0)) &= ~(MTL_OP_MODE_RQS_MASK);
    *MTL_REG(MTL_CHAN_RX_OP_MODE(0)) |= rqs << MTL_OP_MODE_RQS_SHIFT;

    // NOTE - more stuff in dwc_eth_qos that we are skipping regarding to tuning the tqs

    /* Configure MAC */
    *MAC_REG(GMAC_RXQ_CTRL0) &= GMAC_RX_QUEUE_CLEAR(0);
    *MAC_REG(GMAC_RXQ_CTRL0) |= GMAC_RX_DCB_QUEUE_ENABLE(0);

    uint32_t filter = *MAC_REG(GMAC_PACKET_FILTER);

    // Reset all filter flags.
	filter &= ~GMAC_PACKET_FILTER_HMC;
	filter &= ~GMAC_PACKET_FILTER_HPF;
	filter &= ~GMAC_PACKET_FILTER_PCF;
	filter &= ~GMAC_PACKET_FILTER_PM;
	filter &= ~GMAC_PACKET_FILTER_PR;
	filter &= ~GMAC_PACKET_FILTER_RA;

    filter |= GMAC_PACKET_FILTER_PR;

    *MAC_REG(GMAC_PACKET_FILTER) = filter;

    // For now, disabling all flow control. This regsiter controls the generation/reception
    // of the control packets.
    *MAC_REG(GMAC_QX_TX_FLOW_CTRL(0)) = 0;

    // Program all other appropriate fields in MAC_CONFIGURATION
    //       (ie. inter-packet gap, jabber disable).
    uint32_t conf = *MAC_REG(GMAC_CONFIG);
    // Set full duplex mode
    conf |= GMAC_CONFIG_DM;
    // Enable checksum offload
    conf |= GMAC_CONFIG_IPC;

    // Setting the speed of our device to 1000mbps
    conf &= ~( GMAC_CONFIG_PS | GMAC_CONFIG_FES);
    *MAC_REG(GMAC_CONFIG) = conf;

    // Set the MAC Address.

    /* NOTE: We are hardcoding this MAC address to the hardware MAC address of the
    Star64 in the TS machine queue. This address is resident the boards EEPROM, however,
    we need I2C to read from this ROM. */
    *MAC_REG(GMAC_ADDR_HIGH(0)) = 0x00005b75;
    *MAC_REG(GMAC_ADDR_LOW(0)) = 0x0039cf6c;

    /* Configure DMA */

    // Enable operate on second packet
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) |= DMA_CONTROL_OSP;

    // Set the max packet size for rx
    *DMA_REG(DMA_CHAN_RX_CONTROL(0)) &= ~(DMA_RBSZ_MASK << DMA_RBSZ_SHIFT);
    *DMA_REG(DMA_CHAN_RX_CONTROL(0)) |= (MAX_RX_FRAME_SZ << DMA_RBSZ_SHIFT);

    // Program the descriptor length. This is to tell the device that when
    // we reach the base addr + count, we should then wrap back around to
    // the base.

    volatile uint32_t *tx_len_reg = DMA_REG(DMA_CHAN_TX_RING_LEN(0));
    *tx_len_reg = TX_COUNT - 1;
    volatile uint32_t *rx_len = DMA_REG(DMA_CHAN_RX_RING_LEN(0));
    *rx_len = RX_COUNT - 1;

    // Init rx and tx descriptor list addresses.
    tx_desc_base = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);
    rx_desc_base = hw_ring_buffer_paddr;

    *DMA_REG(DMA_CHAN_RX_BASE_ADDR_HI(0)) = rx_desc_base >> 32;
    *DMA_REG(DMA_CHAN_RX_BASE_ADDR(0)) = rx_desc_base & 0xffffffff;
    *DMA_REG(DMA_CHAN_TX_BASE_ADDR_HI(0)) = tx_desc_base >> 32;
    *DMA_REG(DMA_CHAN_TX_BASE_ADDR(0)) = tx_desc_base & 0xffffffff;

    // Enable interrupts.
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) = DMA_CHAN_INTR_NORMAL;

    // Populate the rx and tx hardware rings.
    rx_provide();
    tx_provide();

    // Start DMA and MAC
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) |= DMA_CONTROL_ST;
    *DMA_REG(DMA_CHAN_RX_CONTROL(0)) |= DMA_CONTROL_SR;
    *MAC_REG(GMAC_CONFIG) |= (GMAC_CONFIG_RE | GMAC_CONFIG_TE);

    /* NOTE ------ FROM U-BOOT SOURCE CODE dwc_eth_qos.c:995 */

    /* TX tail pointer not written until we need to TX a packet */
	/*
	 * Point RX tail pointer at last descriptor. Ideally, we'd point at the
	 * first descriptor, implying all descriptors were available. However,
	 * that's not distinguishable from none of the descriptors being
	 * available.
	 */
    *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + (sizeof(struct descriptor) *(RX_COUNT - 1));

}

static void eth_setup(void)
{
    assert((hw_ring_buffer_paddr & 0xFFFFFFFF) == hw_ring_buffer_paddr);

    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

    eth_init();
}

void init(void)
{
    /* De-assert the reset signals that u-boot left asserted. */
#ifdef CONFIG_PLAT_STAR64
    volatile uint32_t *reset_eth = (volatile uint32_t *)(resets + 0x38);
    uint32_t reset_val = *reset_eth;
    uint32_t mask = 0;
    /* U-Boot de-asserts BIT(0) first then BIT(1) when starting up eth0.
        NOTE: This will be different per-board, but this is correct for the
        Pine64 Star64. */
    for (int i = 0; i < 2; i++) {
        reset_val = *reset_eth;
        mask = BIT(i);
        reset_val &= ~mask;
        *reset_eth = reset_val;
    }
#endif /* CONFIG_PLAT_STAR64 */

    // Check if the PHY device is up
    uint32_t phy_stat = *MAC_REG(GMAC_PHYIF_CONTROL_STATUS);
    if (phy_stat & GMAC_PHYIF_CTRLSTATUS_LNKSTS) {
        sddf_dprintf("PHY device is up and running\n");
    } else {
        sddf_dprintf("PHY device is currently down\n");
    }

    if (phy_stat & BIT(16)) {
        sddf_dprintf("PHY device is operating in full duplex mode\n");
    } else {
        sddf_dprintf("PHY device is operating in half duplex mode\n");
    }

    net_queue_init(&rx_queue, (net_queue_t *)rx_free, (net_queue_t *)rx_active, NET_RX_QUEUE_SIZE_DRIV);
    net_queue_init(&tx_queue, (net_queue_t *)tx_free, (net_queue_t *)tx_active, NET_TX_QUEUE_SIZE_DRIV);

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
        sddf_dprintf("ETH|LOG: received notification on unexpected channel %u\n", ch);
        break;
    }
}
