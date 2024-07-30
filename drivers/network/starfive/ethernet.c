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
#include <sddf/network/util.h>
#include <string.h>
#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

uintptr_t eth_regs;
uintptr_t resets;
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;
uintptr_t rx_desc_base;
uintptr_t tx_desc_base;
uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;

#define RX_COUNT 16
#define TX_COUNT 16
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

struct descriptor {
    uint32_t d0;
    uint32_t d1;
    uint32_t d2;
    uint32_t d3;
};

_Static_assert((RX_COUNT + TX_COUNT) * sizeof(struct descriptor) <= HW_REGION_SIZE,
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

static volatile struct mac_regs *mac_regs;
static volatile struct mtl_regs *mtl_regs;
static volatile struct dma_regs *dma_regs;

static inline bool hw_ring_full(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail + 2 - ring->head) % ring_size);
}

static inline bool hw_ring_empty(hw_ring_t *ring, size_t ring_size)
{
    return !((ring->tail - ring->head) % ring_size);
}

static void update_ring_slot(hw_ring_t *ring, unsigned int idx, uint64_t phys,
                            uint32_t d2, uint32_t d3)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    // Place the lower 32 bits of phys in d0
    d->d0 = phys & 0xffffffff;
    // Place the upper 32 bits of phys in d1
    d->d1 = phys >> 32;
    d->d2 = d2;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    THREAD_MEMORY_RELEASE();
    d->d3 = d3;
}

static void rx_provide()
{
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&rx, RX_COUNT) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (rx.tail + 1 == RX_COUNT) {
                cntl |= DESC_RXCTRL_RXRINGEND;
            }

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, buffer.io_or_offset, 0, DESC_RXSTS_OWNBYDMA | BIT(24) | BIT(30));
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            THREAD_MEMORY_RELEASE();
            // *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + sizeof(struct descriptor) * rx.tail;
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
            update_ring_slot(&rx, rx.tail, buffer.io_or_offset, 0, DESC_RXSTS_OWNBYDMA | BIT(24) | BIT(30));
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            rx.head = (rx.head + 1) % RX_COUNT;

            // *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + sizeof(struct descriptor) * rx.tail;
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
            uint32_t tdes3 = (DESC_TXSTS_OWNBYDMA | DESC_TXCTRL_TXFIRST | DESC_TXCTRL_TXLAST | buffer.len);
            tx.descr_mdata[tx.tail] = buffer;

            update_ring_slot(&tx, tx.tail, buffer.io_or_offset, tdes2, tdes3);

            tx.tail = (tx.tail + 1) % TX_COUNT;
            i++;
            /* Set the tail in hardware to the latest tail we have inserted in.
             * This tells the hardware that it has new buffers to send.
             * NOTE: Setting this on every enqueued packet for sanity, change this to once per bactch.
             */
            dma_regs->ch0_txdesc_tail_pointer = tx_desc_base + sizeof(struct descriptor) * (tx.tail);
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
    if (e & DMA_INTR_RI) {
        rx_return();
    }
    if (e & DMA_INTR_TI) {
        tx_return();
    }
    if (e & DMA_INTR_ABNORMAL) {
        if (e & DMA_INTR_FBE) {
            sddf_dprintf("Ethernet device fatal bus error\n");
        }
    }
    *DMA_REG(DMA_CHAN_STATUS(0)) &= e;
}

static void eqos_init()
{
    /* 1. Software reset -- This will reset the MAC internal registers. */
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

    // Enable store and forward mode for TX.
    mtl_regs->txq0_operation_mode |= BIT(1) | (2 << 2);

    // Transmit queue weight
    mtl_regs->txq0_quantum_weight = 0x10;

    // Enable store and forward mode for rx
    mtl_regs->rxq0_operation_mode |= BIT(5);

    /* 2. Program the rx queue to the DMA mapping. */
    uint32_t map0 = *MTL_REG(MTL_RXQ_DMA_MAP0);
    // We only have one queue, and we map it onto DMA channel 0
    map0 &= ~MTL_RXQ_DMA_QXMDMACH_MASK(0);
    map0 |= MTL_RXQ_DMA_QXMDMACH(0, 0);
    *MTL_REG(MTL_RXQ_DMA_MAP0) = map0;


    // Transmit/receive queue fifo size, use all RAM for 1 queue
    uint32_t val = mac_regs->hw_feature1;
    uint32_t tx_fifo_sz;
    uint32_t rx_fifo_sz;
    tx_fifo_sz = (val >> 6) &
		0x1f;
	rx_fifo_sz = (val >> 0) &
		0x1f;

    /* r/tx_fifo_sz is encoded as log2(n / 128). Undo that by shifting */
	tx_fifo_sz = 128 << tx_fifo_sz;
	rx_fifo_sz = 128 << rx_fifo_sz;

	uint32_t tqs = tx_fifo_sz / 256 - 1;
	uint32_t rqs = rx_fifo_sz / 256 - 1;

    mtl_regs->txq0_operation_mode &= ~(0x1ff << 16);
    mtl_regs->txq0_operation_mode |= tqs << 16;
    mtl_regs->rxq0_operation_mode &=  ~(0x3ff << 20);
    mtl_regs->rxq0_operation_mode |= rqs << 20;

    // NOTE - more stuff in dwc_eth_qos that we are skipping regarding to tuning the tqs

    /* Configure MAC */
    mac_regs->rxq_ctrl0 &= ~(3 << 0);
    mac_regs->rxq_ctrl0 |= (1 << 1);

    // /* Multicast and broadcast queue enable */
    // mac_regs->unused_0a4 |= 0x00100000;
    // // /* Enable promise mode */
    // mac_regs->unused_004[1] |= 0x1;

    // /* Set TX flow control parameters */
	// /* Set Pause Time */
    // mac_regs->q0_tx_flow_ctrl |= 0xffff << 16;

    // /* Assign priority for TX flow control */
    // mac_regs->q0_tx_flow_ctrl &= ~(0xff);
    // /* Assign priority for RX flow control */
    // mac_regs->rxq_ctrl2 &= ~(0xff);
	// /* Enable flow control */
    // mac_regs->q0_tx_flow_ctrl |= BIT(1);
    // mac_regs->rx_flow_ctrl |= BIT(0);

    // mac_regs->configuration &= ~(BIT(23) | BIT(19) | BIT(17) | BIT(16));
    // mac_regs->configuration |= (BIT(21) | BIT(20));

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

    /* 3. Program the flow control. */
    // For now, disabling all flow control. This regsiter controls the generation/reception
    // of the control packets.
    *MAC_REG(GMAC_QX_TX_FLOW_CTRL(0)) = 0;

    /* 4. Program the mac interrupt enable register (if applicable). */
    // We don't want to setup interrupts for the MAC component. We will enable
    // them in the DMA componenet

    uint32_t int_en = *MAC_REG(GMAC_INT_EN);
    int_en |= GMAC_INT_DEFAULT_ENABLE | BIT(13) | BIT(14) | BIT(17);
    *MAC_REG(GMAC_INT_EN) = int_en;

    // /* 5. Program all other approrpriate fields in MAC_CONFIGURATION
    //       (ie. inter-packet gap, jabber disable). */
    uint32_t conf = *MAC_REG(GMAC_CONFIG);
    // // Set full duplex mode
    conf |= GMAC_CONFIG_DM;

    // Setting the speed of our device to 100mbps -- THIS LINE IS BROKEN!
    // conf |= GMAC_CONFIG_FES | GMAC_CONFIG_PS;
    *MAC_REG(GMAC_CONFIG) = conf;

    /* Update MAC address*/
    mac_regs->address0_high = 0x00005b75;
    mac_regs->address0_low = 0x0039cf6c;

    // TEMP: Enable MAC interrupts

    /* Configure DMA */
    dma_regs->ch0_tx_control |= BIT(4);

    dma_regs->ch0_rx_control &= ~(0x3fff << 1);
    dma_regs->ch0_rx_control |= (0x600 << 1);

    /* TODO - Desc pad */

	/*
	 * Burst length must be < 1/2 FIFO size.
	 * FIFO size in tqs is encoded as (n / 256) - 1.
	 * Each burst is n * 8 (PBLX8) * 16 (AXI width) == 128 bytes.
	 * Half of n * 256 is n * 128, so pbl == tqs, modulo the -1.
	 */

    uint32_t pbl = tqs + 1;
    if (pbl > 32)
		pbl = 32;
    dma_regs->ch0_tx_control &= ~(0x3f << 16);
    dma_regs->ch0_tx_control |= pbl << 16;

    dma_regs->ch0_rx_control &= ~(0x3f << 16);
    dma_regs->ch0_rx_control |= 8 << 16;

    /* DMA performance configuration */
    val = (2 << 16) | BIT(11) | BIT(3) | BIT(2) | BIT(1);
    dma_regs->sysbus_mode = val;

    volatile uint32_t *tx_len_reg = DMA_REG(DMA_CHAN_TX_RING_LEN(0));
    *tx_len_reg = TX_COUNT;
    volatile uint32_t *rx_len = DMA_REG(DMA_CHAN_RX_RING_LEN(0));
    *rx_len = RX_COUNT;

    /* 5. Init rx and tx descriptor list addresses. */
    tx_desc_base = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);
    rx_desc_base = hw_ring_buffer_paddr;

    *DMA_REG(DMA_CHAN_RX_BASE_ADDR_HI(0)) = rx_desc_base >> 32;
    *DMA_REG(DMA_CHAN_RX_BASE_ADDR(0)) = rx_desc_base & 0xffffffff;
    *DMA_REG(DMA_CHAN_TX_BASE_ADDR_HI(0)) = tx_desc_base >> 32;
    *DMA_REG(DMA_CHAN_TX_BASE_ADDR(0)) = tx_desc_base & 0xffffffff;

    /* 7. Enable interrupts. */
    // Write the interrupt status mask to the DMA Chan Interrupt status register
    // *DMA_REG(DMA_CHAN_INTR_ENA(0)) = DMA_CHAN_INTR_DEFAULT_MASK;
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) = DMA_CHAN_INTR_NORMAL;
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) |= DMA_CHAN_INTR_ABNORMAL | BIT(7);
    // *DMA_REG(DMA_CHAN_INTR_ENA(0)) |= (1 << 15) | (1 << 6);

    /* Populate the rx and tx hardware rings. */
    rx_provide();
    tx_provide();

    /* Start DMA and MAC */
    dma_regs->ch0_tx_control |= BIT(0);
    dma_regs->ch0_rx_control |= BIT(0);
    mac_regs->configuration |= (BIT(1) | BIT(0));

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
    mac_regs = (volatile struct mac_regs *) (eth_regs + MAC_REGS_BASE);
    mtl_regs = (volatile struct mtl_regs *) (eth_regs + MTL_REGS_BASE);
    dma_regs = (volatile struct dma_regs *) (eth_regs + DMA_REGS_BASE);

    assert((hw_ring_buffer_paddr & 0xFFFFFFFF) == hw_ring_buffer_paddr);

    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

    eqos_init();
}

void init(void)
{
    /* De-assert the reset signals that u-boot left asserted. */
    volatile uint32_t *reset_eth = (volatile uint32_t *)(resets + 0x38);
    // sddf_dprintf("This is the value of reset_eth: %u\n", *reset_eth);
    // uint32_t reset_val = *reset_eth;
    // uint32_t mask = 0;
    // /* U-Boot de-asserts BIT(0) first then BIT(1) when starting up eth0. */
    // for (int i = 0; i < 2; i++) {
    //     reset_val = *reset_eth;
    //     mask = BIT(i);
    //     reset_val &= ~mask;
    //     *reset_eth = reset_val;
    // }
    *reset_eth = 0xe0;

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

    net_queue_init(&rx_queue, (net_queue_t *)rx_free, (net_queue_t *)rx_active, RX_QUEUE_SIZE_DRIV);
    net_queue_init(&tx_queue, (net_queue_t *)tx_free, (net_queue_t *)tx_active, TX_QUEUE_SIZE_DRIV);

        eth_setup();


    microkit_irq_ack(IRQ_CH);
}

void notified(microkit_channel ch)
{
    switch (ch) {
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
    default:
        sddf_dprintf("ETH|LOG: received notification on unexpected channel %u\n", ch);
        break;
    }
}
