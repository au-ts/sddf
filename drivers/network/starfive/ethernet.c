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

uintptr_t eth_regs;
uintptr_t resets;
uintptr_t hw_ring_buffer_vaddr;
uintptr_t hw_ring_buffer_paddr;

uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;

#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

struct descriptor {
    uint32_t status;
    uint32_t cntl;
    uint32_t addr;
    uint32_t next;
};

_Static_assert((RX_COUNT + TX_COUNT) * sizeof(struct descriptor) <= HW_REGION_SIZE,
               "Expect rx+tx buffers to fit in single 2MB page");

typedef struct {
    unsigned int tail; /* index to insert at */
    unsigned int head; /* index to remove from */
    net_buff_desc_t descr_mdata[MAX_COUNT]; /* associated meta data array */
    volatile struct descriptor *descr; /* buffer descripter array */
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
        while (!hw_ring_full(&rx, RX_COUNT) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (rx.tail + 1 == RX_COUNT) {
                cntl |= DESC_RXCTRL_RXRINGEND;
            }

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, DESC_RXSTS_OWNBYDMA, cntl, buffer.io_or_offset, 0);
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = hw_ring_buffer_paddr + sizeof(struct descriptor) * rx.tail;
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
        if (d->status & DESC_RXSTS_OWNBYDMA) {
            break;
        }
        net_buff_desc_t buffer = rx.descr_mdata[rx.head];
        THREAD_MEMORY_ACQUIRE();

        if (d->status & DESC_RXSTS_ERROR) {
            sddf_dprintf("ETH|ERROR: RX descriptor returned with error status %x\n", d->status);
            uint32_t cntl = (MAX_RX_FRAME_SZ << DESC_RXCTRL_SIZE1SHFT) & DESC_RXCTRL_SIZE1MASK;
            if (rx.tail + 1 == RX_COUNT) {
                cntl |= DESC_RXCTRL_RXRINGEND;
            }

            rx.descr_mdata[rx.tail] = buffer;
            update_ring_slot(&rx, rx.tail, DESC_RXSTS_OWNBYDMA, cntl, buffer.io_or_offset, 0);
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            *DMA_REG(DMA_CHAN_RX_TAIL_ADDR(0)) = hw_ring_buffer_paddr + sizeof(struct descriptor) * rx.tail;
        } else {
            buffer.len = (d->status & DESC_RXSTS_LENMSK) >> DESC_RXSTS_LENSHFT;
            int err = net_enqueue_active(&rx_queue, buffer);
            assert(!err);
            packets_transferred = true;
        }
        rx.head = (rx.head + 1) % RX_COUNT;
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

            uint32_t cntl = (((uint32_t) buffer.len) << DESC_TXCTRL_SIZE1SHFT) & DESC_TXCTRL_SIZE1MASK;
            cntl |= DESC_TXCTRL_TXLAST | DESC_TXCTRL_TXFIRST | DESC_TXCTRL_TXINT;
            if (tx.tail + 1 == TX_COUNT) {
                cntl |= DESC_TXCTRL_TXRINGEND;
            }
            tx.descr_mdata[tx.tail] = buffer;
            update_ring_slot(&tx, tx.tail, DESC_TXSTS_OWNBYDMA, cntl, buffer.io_or_offset, 0);

            tx.tail = (tx.tail + 1) % TX_COUNT;
            i++;
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_ring_full(&tx, TX_COUNT) && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }
    /* Set the tail in hardware to the latest tail we have inserted in.
    This tells the hardware that it has new buffers to send. */
    *DMA_REG(DMA_CHAN_TX_TAIL_ADDR(0)) = hw_ring_buffer_paddr + RX_COUNT + sizeof(struct descriptor) * tx.tail;
}

static void tx_return(void)
{
    bool enqueued = false;
    while (!hw_ring_empty(&tx, TX_COUNT)) {
        /* Ensure that this buffer has been sent by the device */
        volatile struct descriptor *d = &(tx.descr[tx.head]);
        if (d->status & DESC_TXSTS_OWNBYDMA) {
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
    sddf_dprintf("handling irq\n");
    uint32_t e = *DMA_REG(DMA_CHAN_STATUS(0));
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
    // uint32_t mode = *DMA_REG(DMA_BUS_MODE);
    // mode |= DMA_BUS_MODE_SFT_RESET;
    // *DMA_REG(DMA_BUS_MODE) = 15000;

    volatile uint32_t *mode = DMA_REG(DMA_BUS_MODE);
    *mode |= DMA_BUS_MODE_SFT_RESET;
    sddf_dprintf("This is the value of mode: %x\n", *mode);

    // Poll on BIT 0. This bit is cleared by the device when the reset is complete.
    while(1) {
        sddf_dprintf("looping\n");
        mode = DMA_REG(DMA_BUS_MODE);
        if (!(*mode & DMA_BUS_MODE_SFT_RESET)) {
            sddf_dprintf("This is the value of DMA_BUS_MODE: %x\n", *mode);
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
    volatile uint32_t *rx_base_addr_reg = DMA_REG(DMA_CHAN_RX_BASE_ADDR(0));
    *rx_base_addr_reg = hw_ring_buffer_paddr;
    volatile uint32_t *tx_base_addr_reg = DMA_REG(DMA_CHAN_TX_BASE_ADDR(0));
    *tx_base_addr_reg = hw_ring_buffer_paddr + (sizeof(struct descriptor) * RX_COUNT);
    sddf_dprintf("This is the hwring buffer paddr: %p and this is the rx base: %p\n", hw_ring_buffer_paddr, *rx_base_addr_reg);
    /* 6. Program settings for _CONTROL, _TX_CONTROL, _RX_CONTROL
          registers. */
    // Disable control features for 8xPBL mode and Descriptor Skip Length
    *DMA_REG(DMA_CHAN_CONTROL(0)) = 0;

    uint32_t tx_chan_ctrl = 0;
    // Setting this bit ignores the PBL requirement
    tx_chan_ctrl |= DMA_BUS_MODE_PBL;
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) = tx_chan_ctrl;

    // TODO: I don't believe there is anything for us to enable in rx
    // chan control. Double check this.

    /* 7. Enable interrupts. */
    *DMA_REG(DMA_CHAN_INTR_ENA(0)) |= DMA_INTR_MASK;

    /* 8. Start tx and rx DMAs. */
    *DMA_REG(DMA_CHAN_TX_CONTROL(0)) |= DMA_CONTROL_ST;
    *DMA_REG(DMA_CHAN_RX_CONTROL(0)) |= DMA_CONTROL_SR;

    /* NOTE: Repeat these above steps for all of the tx and rx channels
        that we are using. For now we are going to keep this to one pair.*/
}

static void mtl_init(void)
{
    /* 1. Program the tx scheduling and recv arbitration algo fields in the
          MTL_Operation_mode reg. */
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

    // TODO: don't just use '0' here
    uint32_t txq0_op_mode = *MTL_REG(0);

    // We use the store-and-forward DMA mode
    txq0_op_mode |= MTL_OP_MODE_TSF;

    // Enable the TX queue
    txq0_op_mode &= ~MTL_OP_MODE_TXQ_ENABLE_MASK;
    txq0_op_mode |= MTL_OP_MODE_TXQ_ENABLE;

    // Set the TX queue size
    txq0_op_mode &= ~MTL_OP_MODE_TQS_MASK;
    // TODO: unsure if we need to set TX queue size as we only
    // have one queue and the documentation says that the queue size
    // field is read-only unless you have more than one queue.

    *MTL_REG(0) = txq0_op_mode;

    /* 4. Do the same as the above for RX in the MTL_TX_Opeartion_mode reg. */

    uint32_t rxq0_op_mode = *MTL_REG(0x30);
    // Use store-and-forward DMA mode
    rxq0_op_mode |= MTL_OP_MODE_RSF;

    // Set the RX queue size
    // TODO: We do not set the RX queue size since we only have one queue
    sddf_dprintf("RX queue size: )0x%lx\n", (rxq0_op_mode & MTL_OP_MODE_RQS_MASK) >> 20);

    // TODO: for now we ignore setting flow control

    *MTL_REG(0x30) = rxq0_op_mode;

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
    // For now, disabling all flow control
    *MAC_REG(GMAC_QX_TX_FLOW_CTRL(0)) = 0;

    /* 4. Program the mac interrupt enable register (if applicable). */
    // We don't want to setup interrupts for the MAC component. We will enable
    // them in the DMA componenet

    uint32_t int_en = *MAC_REG(GMAC_INT_EN);
    int_en = 0;
    *MAC_REG(GMAC_INT_EN) = int_en;

    /* 5. Program all other approrpriate fields in MAC_CONFIGURATION
          (ie. inter-packet gap, jabber diable). */
    uint32_t conf = *MAC_REG(GMAC_CONFIG);
    // Set full duplex mode
    conf |= GMAC_CONFIG_DM;
    *MAC_REG(GMAC_CONFIG) = conf;

    /* 6. Set bit 0 and 1 in MAC_CONFIGURATION to start the MAC transmitter
          and receiver. */
    conf = *MAC_REG(GMAC_CONFIG);
    conf |= GMAC_CONFIG_RE;
    *MAC_REG(GMAC_CONFIG) = conf;
}

static void eth_setup(void)
{
    volatile uint32_t *mac_version = ((volatile uint32_t *)(eth_regs + 0x00000110));
    volatile uint32_t *mac_debug = ((volatile uint32_t *)(eth_regs + GMAC_DEBUG));
    sddf_dprintf("Beginning eth setup. This is the mac version: %x --- this is the mac debug reg: %x\n", *mac_version, *mac_debug);
    /* Save the MAC address. This address should have been populated by u-boot. We will
    just restore these when setting up the MAC component of the eth device. */
    mac_regs = (volatile struct mac_regs *) (eth_regs + MAC_REGS_BASE);
    mtl_regs = (volatile struct mtl_regs *) (eth_regs + MTL_REGS_BASE);
    dma_regs = (volatile struct dma_regs *) (eth_regs + DMA_REGS_BASE);

    dma_regs->mode |= DMA_BUS_MODE_SFT_RESET;
    while(dma_regs->mode & DMA_BUS_MODE_SFT_RESET) {
        sddf_dprintf("waiting for reset\n");
    }

    sddf_dprintf("This is hardware features: %x\n", mac_regs->hw_feature0);

    uint32_t l = mac_regs->address0_low;
    uint32_t h = mac_regs->address0_high;
    writel(0xfafafafa, &mac_regs->address0_low);
    writel(0xafafafaf, &mac_regs->address0_high);

    uint32_t test = readl(&mac_regs->address0_low);
    sddf_dprintf("This is the test value of addr low: %x\n", test);

    sddf_dprintf("This is the addr of mac_regs: %p ---- mtl_regs: %p ---- dma_regs: %p\n", mac_regs, mtl_regs, dma_regs);

    sddf_dprintf("This is the value of the config reg: %x\n", mac_regs->configuration);

    assert((hw_ring_buffer_paddr & 0xFFFFFFFF) == hw_ring_buffer_paddr);

    rx.descr = (volatile struct descriptor *)hw_ring_buffer_vaddr;
    tx.descr = (volatile struct descriptor *)(hw_ring_buffer_vaddr + (sizeof(struct descriptor) * RX_COUNT));

    /* 1. Init DMA */
    dma_init();

    /* 2. Init MTL */
    mtl_init();

    /* 3. Init MAC */
    mac_init(0xff35, 0xddaa);

    sddf_dprintf("This is mac high: %x -- and mac low: %x\n", mac_regs->address0_high, mac_regs->address0_low);


    sddf_dprintf("Finished eth setup\n");
}

void init(void)
{
    /* De-assert the reset signals that u-boot left asserted. */
    volatile uint32_t *reset_eth = (volatile uint32_t *)(resets + 0x38);
    sddf_dprintf("This is the value of reset_eth: %u\n", *reset_eth);
    *reset_eth = 0;
    eth_setup();

    net_queue_init(&rx_queue, (net_queue_t *)rx_free, (net_queue_t *)rx_active, RX_QUEUE_SIZE_DRIV);
    net_queue_init(&tx_queue, (net_queue_t *)tx_free, (net_queue_t *)tx_active, TX_QUEUE_SIZE_DRIV);

    rx_provide();
    tx_provide();

    microkit_irq_ack(IRQ_CH);
    sddf_dprintf("Finished eth init\n");
}

void notified(microkit_channel ch)
{
    sddf_dprintf("we got a notification\n");
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
