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

// struct descriptor {
//     uint32_t status;
//     uint32_t cntl;
//     uint32_t addr;
//     uint32_t next;
// };
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
            // update_ring_slot(&rx, rx.tail, DESC_RXSTS_OWNBYDMA | BIT(30) | BIT(24), buffer.len, buffer.io_or_offset, 0);
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
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
            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (rx.tail + 1 == RX_COUNT) {
                cntl |= DESC_RXCTRL_RXRINGEND;
            }

            rx.descr_mdata[rx.tail] = buffer;
            // update_ring_slot(&rx, rx.tail, DESC_RXSTS_OWNBYDMA | BIT(24), cntl, buffer.io_or_offset, 0);
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            rx.head = (rx.head + 1) % RX_COUNT;

            *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + sizeof(struct descriptor) * rx.tail;
        } else {
            buffer.len = (d->d3 & DESC_RXSTS_LENMSK) >> DESC_RXSTS_LENSHFT;
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

            uint32_t d2 = DESC_TXCTRL_TXINT | buffer.len;
            sddf_dprintf("-------------- New transmit ------------\n");
            sddf_dprintf("This is the current TX descr: %p\n", *DMA_REG(DMA_CHAN_CUR_TX_DESC(0)));
            sddf_dprintf("This is the current tx buffer for DMA: %p\n", *DMA_REG(DMA_CHAN_CUR_TX_BUF_ADDR(0)));
            sddf_dprintf("This is the value of the DMA debug status 0 register %b\n", *DMA_REG(DMA_DEBUG_STATUS_0));
            sddf_dprintf("This is the current tail pointer: %p\n", *DMA_REG(DMA_CHAN_TX_TAIL_ADDR(0)));
            sddf_dprintf("This is the tail we are operating on: %d\n", tx.tail);
            tx.descr_mdata[tx.tail] = buffer;
            update_ring_slot(&tx, tx.tail, buffer.io_or_offset, d2, (DESC_TXSTS_OWNBYDMA | BIT(29) | BIT(28)));

            tx.tail = (tx.tail + 1) % TX_COUNT;
            i++;
            /* Set the tail in hardware to the latest tail we have inserted in.
             * This tells the hardware that it has new buffers to send.
             * NOTE: Setting this on every enqueued packet for sanity, change this to once per bactch.
             */
            *DMA_REG(DMA_CHAN_TX_TAIL_ADDR(0)) = tx_desc_base + sizeof(struct descriptor) * (tx.tail);
            sddf_dprintf("This is the value of the mtl tx operation mode: %b\n", mtl_regs->txq0_operation_mode);
            sddf_dprintf("This is the value of the MTL transmit debug registe: %b\n", mtl_regs->txq0_debug);
            sddf_dprintf("This is the value of the MTL rx debug register: %b\n", mtl_regs->rxq0_debug);
            sddf_dprintf("This is the value of the MAC debug register: %b\n", *MAC_REG(GMAC_DEBUG));
            sddf_dprintf("This is the value of the MTL FIFO debug status register: %b\n", *MTL_REG(0x00000c0c));
            sddf_dprintf("This is the value of the MTL FIFO debug data register: %b\n", *MTL_REG(0x00000c10));
            sddf_dprintf("This is the value of the DMA debug status 0 register %b\n", *DMA_REG(DMA_DEBUG_STATUS_0));
            sddf_dprintf("This is the new tail addr: %p --- this is the size of the desc struct: %x -- this is the tail index: %d -- this is the buffer addr: %p\n", \
            hw_ring_buffer_paddr + ((sizeof(struct descriptor) * (RX_COUNT + tx.tail))), sizeof(struct descriptor), tx.tail, buffer.io_or_offset);
            sddf_dprintf("This is the current tx buffer for DMA: %p\n", *DMA_REG(DMA_CHAN_CUR_TX_BUF_ADDR(0)));
            sddf_dprintf("This is the current TX descr: %p\n", *DMA_REG(DMA_CHAN_CUR_TX_DESC(0)));
            sddf_dprintf("This is the DMA Channel 0 Status: %b\n", *DMA_REG(DMA_CHAN_STATUS(0)));
            sddf_dprintf("This is the average traffic on the MTL: %x\n", *MTL_REG(0xd14));
            sddf_dprintf("-------------- End transmit ------------\n");

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
    sddf_dprintf("handling irq: %b\n",e);
    sddf_dprintf("This is the DMA interrupt status register: %b\n", *DMA_REG(DMA_STATUS));

    if (e & DMA_INTR_RI) {
        sddf_dprintf("recv complete\n");
        rx_return();
    }
    if (e & DMA_INTR_TI) {
        sddf_dprintf("transmit complete\n");
        tx_return();
    }
    if (e & DMA_INTR_ABNORMAL) {
        sddf_dprintf("abnormal response\n");
        if (e & DMA_INTR_FBE) {
            sddf_dprintf("Ethernet device fatal bus error\n");
        }
    }

    *DMA_REG(DMA_CHAN_STATUS(0)) &= e;
}

static void dma_init(void)
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

    /* 2. Init sysbus mode. */
    volatile uint32_t *sysbus_mode_reg = DMA_REG(DMA_SYS_BUS_MODE);
    // Set the fixed length burst to 8
    *sysbus_mode_reg |= DMA_SYS_BUS_FB;
    *sysbus_mode_reg |= DMA_AXI_BLEN8;

    /* 3. Create desc lists for rx and tx. */

    /* 4. Program tx and rx ring length registers. */
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

    /* NOTE ------ FROM U-BOOT SOURCE CODE dwc_eth_qos.c:995 */

    *DMA_REG(DMA_CHAN_TX_TAIL_ADDR(0)) = tx_desc_base;
    /* TX tail pointer not written until we need to TX a packet */
	/*
	 * Point RX tail pointer at last descriptor. Ideally, we'd point at the
	 * first descriptor, implying all descriptors were available. However,
	 * that's not distinguishable from none of the descriptors being
	 * available.
	 */

    // Zero out the rx desc region
    memset((void *) rx.descr, 0, sizeof(struct descriptor) * RX_COUNT);

    *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = rx_desc_base + (sizeof(struct descriptor) *(RX_COUNT - 1));

    // sddf_dprintf("This is the hwring buffer paddr: %p and this is the tx base: %p\n", rx_desc_base, tx_desc_base);
    /* 6. Program settings for _CONTROL, _TX_CONTROL, _RX_CONTROL
          registers. */
    // Disable control features for 8xPBL mode and Descriptor Skip Length
    *DMA_REG(DMA_CHAN_CONTROL(0)) = BIT(16);

    uint32_t tx_chan_ctrl = 0;
    // Setting this bit ignores the PBL requirement
    tx_chan_ctrl |= DMA_BUS_MODE_PBL;
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) = tx_chan_ctrl;

    // Set the buffer size in the rx chan control registers
    uint32_t rx_chan_ctrl = *DMA_REG(DMA_CHAN_RX_CONTROL(0));
    rx_chan_ctrl &= 0x3fff << 1;
    rx_chan_ctrl |= NET_BUFFER_SIZE << 1;

    /* 7. Enable interrupts. */
    // Write the interrupt status mask to the DMA Chan Interrupt status register
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) = DMA_CHAN_INTR_DEFAULT_MASK;
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) |= DMA_CHAN_INTR_NORMAL;


    /* 8. Start tx and rx DMAs. */
    uint32_t tx_ctrl = *DMA_REG(DMA_CHAN_TX_CONTROL(0));
    tx_ctrl |= DMA_CONTROL_ST;
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) = tx_ctrl;
    uint32_t rx_ctrl = *DMA_REG(DMA_CHAN_RX_CONTROL(0));
    rx_ctrl |= DMA_CONTROL_SR;
    *DMA_REG(DMA_CHAN_RX_CONTROL(0)) = rx_ctrl;

    /* NOTE: Repeat these above steps for all of the tx and rx channels
        that we are using. For now we are going to keep this to one pair.*/
}

static void mtl_init(void)
{
    /* 1. Program the tx scheduling and recv arbitration algo fields in the
          MTL_Operation_mode reg - IN THE CASE OF MULTIPLE Tx AND Rx QUEUES. */
    uint32_t val = *MTL_REG(MTL_OPERATION_MODE);

    val &= ~MTL_OPERATION_RAA;
    val &= ~MTL_OPERATION_SCHALG_MASK;

    // TODO: Figure out correct rx algo to use
    val |= MTL_OPERATION_RAA_SP;

    // TODO: Figure out correct tx sched algo
    val |= MTL_OPERATION_SCHALG_SP;

    *MTL_REG(MTL_OPERATION_MODE) = val;

    /* 2. Program the rx queue to the DMA mapping. */
    uint32_t map0 = *MTL_REG(MTL_RXQ_DMA_MAP0);
    // We only have one queue, and we map it onto DMA channel 0
    map0 &= ~MTL_RXQ_DMA_QXMDMACH_MASK(0);
    map0 |= MTL_RXQ_DMA_QXMDMACH(0, 0);
    *MTL_REG(MTL_RXQ_DMA_MAP0) = map0;

    /* 3. Program the TSF, TQE, TQS fields in the MTL_TX_Opeartion_mode reg. */

    // uint32_t txq0_op_mode = mtl_regs->txq0_operation_mode;
    uint32_t txq0_op_mode = *MTL_REG(MTL_CHAN_TX_OP_MODE(0));
    sddf_dprintf("This is the mtl tx operation mode: %b\n", txq0_op_mode);
    // We use the store-and-forward DMA mode
    txq0_op_mode = MTL_OP_MODE_TSF;

    // Enable the TX queue. This field is apprently read only in single queue configurations.
    txq0_op_mode &= ~MTL_OP_MODE_TXQ_ENABLE_MASK;
    txq0_op_mode |= MTL_OP_MODE_TXQ_ENABLE;

    *MTL_REG(MTL_CHAN_TX_OP_MODE(0)) = txq0_op_mode;

    /* 4. Do the same as the above for RX in the MTL_RX_Opeartion_mode reg. */

    uint32_t rxq0_op_mode = *MTL_REG(MTL_CHAN_RX_OP_MODE(0));
    // Use store-and-forward DMA mode
    rxq0_op_mode |= MTL_OP_MODE_RSF;

    // Set the RX queue size
    // TODO: We do not set the RX queue size since we only have one queue
    // sddf_dprintf("RX queue size: )0x%lx\n", (rxq0_op_mode & MTL_OP_MODE_RQS_MASK) >> 20);

    // TODO: for now we ignore setting flow control

    *MTL_REG(MTL_CHAN_RX_OP_MODE(0)) = rxq0_op_mode;

    /* NOTE: We repeate steps 3 and 4 for the amount of tx and rx queues we are
        using in our system. For now this is just one. */
}

static void mac_init(uint32_t machi, uint32_t maclo)
{
    /* 1. Provide mac address. */
    // NOTE: Can we assume that U-Boot has already populated these registers. In that
    // case can we just save these registers before we do a DMA reset?
    *MAC_REG(GMAC_ADDR_HIGH(0)) = machi;
    *MAC_REG(GMAC_ADDR_LOW(0)) = maclo;

    /* 2. Program the packet filter. */
    // Set the program filter to Promiscuous mode. In this mode the NIC will pass all
    // network traffic us.

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

    /* 5. Program all other approrpriate fields in MAC_CONFIGURATION
          (ie. inter-packet gap, jabber disable). */
    uint32_t conf = *MAC_REG(GMAC_CONFIG);
    // sddf_dprintf("This is the standard value of the mac config register: %x\n", conf);
    // Set full duplex mode
    conf |= GMAC_CONFIG_DM;
    // Setting the speed of our device to 100mbps
    conf |= GMAC_CONFIG_FES | GMAC_CONFIG_PS;
    *MAC_REG(GMAC_CONFIG) = conf;

    /* 6. Set bit 0 and 1 in MAC_CONFIGURATION to start the MAC transmitter
          and receiver. */
    conf = *MAC_REG(GMAC_CONFIG);
    conf |= (GMAC_CONFIG_RE | GMAC_CONFIG_TE);
    *MAC_REG(GMAC_CONFIG) = conf;
}

static void eth_init(uint32_t machi, uint32_t maclo)
{
    volatile uint32_t *mode = DMA_REG(DMA_BUS_MODE);
    *mode |= DMA_BUS_MODE_SFT_RESET;
    // sddf_dprintf("This is the value of mode: %x\n", *mode);

    // Poll on BIT 0. This bit is cleared by the device when the reset is complete.
    while(1) {
        // sddf_dprintf("looping\n");
        mode = DMA_REG(DMA_BUS_MODE);
        if (!(*mode & DMA_BUS_MODE_SFT_RESET)) {
            // sddf_dprintf("This is the value of DMA_BUS_MODE: %x\n", *mode);
            break;
        }
    }

    mtl_init();

    /* MAC INIT */
    /* 1. Provide mac address. */
    // NOTE: Can we assume that U-Boot has already populated these registers. In that
    // case can we just save these registers before we do a DMA reset?
    *MAC_REG(GMAC_ADDR_HIGH(0)) = machi;
    *MAC_REG(GMAC_ADDR_LOW(0)) = maclo;

    /* 2. Program the packet filter. */
    // Set the program filter to Promiscuous mode. In this mode the NIC will pass all
    // network traffic us.

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

    /* 5. Program all other approrpriate fields in MAC_CONFIGURATION
          (ie. inter-packet gap, jabber disable). */
    uint32_t conf = *MAC_REG(GMAC_CONFIG);
    // sddf_dprintf("This is the standard value of the mac config register: %x\n", conf);
    // Set full duplex mode
    conf |= GMAC_CONFIG_DM;
    // Setting the speed of our device to 100mbps
    conf |= GMAC_CONFIG_FES | GMAC_CONFIG_PS;
    *MAC_REG(GMAC_CONFIG) = conf;


    /* DMA INIT*/

  /* 2. Init sysbus mode. */
    volatile uint32_t *sysbus_mode_reg = DMA_REG(DMA_SYS_BUS_MODE);
    // Set the fixed length burst to 8
    *sysbus_mode_reg |= DMA_SYS_BUS_FB;
    *sysbus_mode_reg |= DMA_AXI_BLEN8;

    /* 3. Create desc lists for rx and tx. */

    /* 4. Program tx and rx ring length registers. */
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



    // sddf_dprintf("This is the hwring buffer paddr: %p and this is the tx base: %p\n", rx_desc_base, tx_desc_base);
    /* 6. Program settings for _CONTROL, _TX_CONTROL, _RX_CONTROL
          registers. */
    // Disable control features for 8xPBL mode and Descriptor Skip Length
    *DMA_REG(DMA_CHAN_CONTROL(0)) = BIT(16);

    uint32_t tx_chan_ctrl = 0;
    // Setting this bit ignores the PBL requirement
    tx_chan_ctrl |= DMA_BUS_MODE_PBL | BIT(4);
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) = tx_chan_ctrl;

    // Set the buffer size in the rx chan control registers
    uint32_t rx_chan_ctrl = *DMA_REG(DMA_CHAN_RX_CONTROL(0));
    rx_chan_ctrl &= 0x3fff << 1;
    rx_chan_ctrl |= NET_BUFFER_SIZE << 1;

    /* 7. Enable interrupts. */
    // Write the interrupt status mask to the DMA Chan Interrupt status register
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) = DMA_CHAN_INTR_DEFAULT_MASK;
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) |= DMA_CHAN_INTR_NORMAL;


    /* 8. Start tx and rx DMAs. */
    uint32_t tx_ctrl = *DMA_REG(DMA_CHAN_TX_CONTROL(0));
    tx_ctrl |= DMA_CONTROL_ST;
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) = tx_ctrl;
    uint32_t rx_ctrl = *DMA_REG(DMA_CHAN_RX_CONTROL(0));
    rx_ctrl |= DMA_CONTROL_SR;
    *DMA_REG(DMA_CHAN_RX_CONTROL(0)) = rx_ctrl;

    /* NOTE: Repeat these above steps for all of the tx and rx channels
        that we are using. For now we are going to keep this to one pair.*/
    /* 6. Set bit 0 and 1 in MAC_CONFIGURATION to start the MAC transmitter
          and receiver. */
    conf = *MAC_REG(GMAC_CONFIG);
    conf |= (GMAC_CONFIG_RE | GMAC_CONFIG_TE);
    *MAC_REG(GMAC_CONFIG) = conf;

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
    mac_regs->rxq_ctrl0 |= (2 << 0);

    /* Multicast and broadcast queue enable */
    mac_regs->unused_0a4 |= 0x00100000;
    /* Enable promise mode */
    mac_regs->unused_004[1] |= 0x1;

    /* Set TX flow control parameters */
	/* Set Pause Time */
    mac_regs->q0_tx_flow_ctrl |= 0xffff << 16;

    /* Assign priority for TX flow control */
    mac_regs->q0_tx_flow_ctrl &= ~(0xff);
    /* Assign priority for RX flow control */
    mac_regs->rxq_ctrl2 &= ~(0xff);
	/* Enable flow control */
    mac_regs->q0_tx_flow_ctrl |= BIT(1);
    mac_regs->rx_flow_ctrl |= BIT(0);

    mac_regs->configuration &= ~(BIT(23) | BIT(19) | BIT(17) | BIT(16));
    mac_regs->configuration |= (BIT(21) | BIT(20));

    /* Update MAC address*/
    mac_regs->address0_high = 0x00005b75;
    mac_regs->address0_low = 0x0039cf6c;

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
    volatile uint32_t *mac_version = ((volatile uint32_t *)(eth_regs + 0x00000110));
    volatile uint32_t *mac_debug = ((volatile uint32_t *)(eth_regs + GMAC_DEBUG));
    sddf_dprintf("Beginning eth setup. This is the mac version: %x --- this is the mac debug reg: %x\n", *mac_version, *mac_debug);
    volatile uint32_t *txp_control_status = MTL_REG(0x00000ca0);
    sddf_dprintf("This mtl register should be none zero: %x\n", *txp_control_status);
    volatile uint32_t *mtl_config = MTL_REG(0x00000c00);
    *mtl_config = 0x2;
    sddf_dprintf("This mtl config register should be none zero: %x\n", *mtl_config);
    volatile uint32_t *dma_sysbusmode = DMA_REG(DMA_SYS_BUS_MODE);
    sddf_dprintf("This dma register shold be none zero: %x\n", *dma_sysbusmode);
    /* Save the MAC address. This address should have been populated by u-boot. We will
    just restore these when setting up the MAC component of the eth device. */
    mac_regs = (volatile struct mac_regs *) (eth_regs + MAC_REGS_BASE);
    mtl_regs = (volatile struct mtl_regs *) (eth_regs + MTL_REGS_BASE);
    dma_regs = (volatile struct dma_regs *) (eth_regs + DMA_REGS_BASE);

    dma_regs->mode |= DMA_BUS_MODE_SFT_RESET;
    while(dma_regs->mode & DMA_BUS_MODE_SFT_RESET) {
        sddf_dprintf("waiting for reset\n");
    }
    *MTL_REG(0x00000c08) = (BIT(0) | BIT(1));
    assert((hw_ring_buffer_paddr & 0xFFFFFFFF) == hw_ring_buffer_paddr);

    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

    // eqos_init();
    eth_init(0x00005b75, 0x0039cf6c);

    /* 1. Init DMA */
    // dma_init();

    /* 2. Init MTL */
    // mtl_init();

    /* 3. Init MAC */
    // NOTE: These are hardcoded MAC addresses for our board. The MAC addresses for this device
    // exists in the EEPROM. We need an i2c driver for the star64 to read from the EEPROM.
    // mac_init(0x00005b75, 0x0039cf6c);
    sddf_dprintf("This is the value of the DMA debug status 0 register AT THE END OF ETH_SETUP %b\n", *DMA_REG(DMA_DEBUG_STATUS_0));

    // sddf_dprintf("This is the value of the mac config reg: %b\n", mac_regs->configuration);

    // sddf_dprintf("Finished eth setup\n");
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
    eth_setup();

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

    // rx_provide();
    // sddf_dprintf("This is the value of the DMA debug status 0 register AFTER RX PROVIDE %b\n", *DMA_REG(DMA_DEBUG_STATUS_0));
    tx_provide();

    microkit_irq_ack(IRQ_CH);
    // sddf_dprintf("Finished eth init\n");

}

void notified(microkit_channel ch)
{
    sddf_dprintf("we got a notification\n");
    // sddf_dprintf("This is the value of the MTL transmit debug registe: %b\n", mtl_regs->txq0_debug);
    // sddf_dprintf("This is the value of the MTL rx debug register: %b\n", mtl_regs->rxq0_debug);
    // sddf_dprintf("This is the value of the MAC debug register: %b\n", *MAC_REG(GMAC_DEBUG));
    // sddf_dprintf("This is the value of the DMA debug status 0 register %b\n", *DMA_REG(DMA_DEBUG_STATUS_0));
    // sddf_dprintf("This is the value of the DMA debug status 1 register %b\n", *DMA_REG(DMA_DEBUG_STATUS_1));

    switch (ch) {
    case IRQ_CH:
        microkit_dbg_puts("recv an irq\n");
        handle_irq();
        microkit_irq_ack_delayed(ch);
        break;
    case RX_CH:
        microkit_dbg_puts("rx ch\n");
        rx_provide();
        break;
    case TX_CH:
        microkit_dbg_puts("tx ch\n");
        tx_provide();
        break;
    default:
        sddf_dprintf("ETH|LOG: received notification on unexpected channel %u\n", ch);
        break;
    }
}