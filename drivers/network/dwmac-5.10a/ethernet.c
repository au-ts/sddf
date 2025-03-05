/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>

#include "ethernet.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

__attribute__((__section__(".net_driver_config"))) net_driver_config_t config;

#ifdef CONFIG_PLAT_STAR64
// @kwinter: Figure out how to get this to work with the new elf patching.
uintptr_t resets = 0x3000000;
#endif /* CONFIG_PLAT_STAR64 */

#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

struct descriptor {
    uint32_t addr_low;
    uint32_t addr_high;
    uint32_t des2;
    uint32_t des3;
};

typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of the ring */
    volatile struct descriptor *descr; /* buffer descripter array */
} hw_ring_t;

hw_ring_t rx;
hw_ring_t tx;

uintptr_t rx_desc_base;
uintptr_t tx_desc_base;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

uintptr_t eth_regs;

static inline bool hw_ring_full(hw_ring_t *ring)
{
    return ring->tail - ring->head == ring->capacity;
}

static inline bool hw_ring_empty(hw_ring_t *ring)
{
    return ring->tail - ring->head == 0;
}

static void update_ring_slot(hw_ring_t *ring, unsigned int idx, uint32_t addr_low, uint32_t addr_high, uint32_t des2,
                             uint32_t des3)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->addr_low = addr_low;
    d->addr_high = addr_high;
    d->des2 = des2;
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    THREAD_MEMORY_RELEASE();
    d->des3 = des3;
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
            update_ring_slot(&rx, idx, buffer.io_or_offset, buffer.io_or_offset >> 32, 0,
                             DESC_RXSTS_OWNBYDMA | DESC_RXSTS_BUFFER1_ADDR_VALID | DESC_RXSTS_IOC);
            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            THREAD_MEMORY_RELEASE();
            *DMA_REG(DMA_CH0_RXDESC_TAIL_PTR) = rx_desc_base + sizeof(struct descriptor) * rx.tail;
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
        if (d->des3 & DESC_RXSTS_OWNBYDMA) {
            break;
        }

        THREAD_MEMORY_ACQUIRE();

        if (d->des3 & DESC_RXSTS_ERROR) {
            sddf_dprintf("ETH|ERROR: RX descriptor returned with error status %x\n", d->des3);
            idx = rx.tail % rx.capacity;
            update_ring_slot(&rx, idx, d->addr_low, d->addr_high, 0,
                             DESC_RXSTS_OWNBYDMA | DESC_RXSTS_BUFFER1_ADDR_VALID | DESC_RXSTS_IOC);

            /* We will update the hardware register that stores the tail address. This tells
            the device that we have new descriptors to use. */
            *DMA_REG(DMA_CH0_RXDESC_TAIL_PTR) = rx_desc_base + sizeof(struct descriptor) * idx;
            rx.tail++;
        } else {
            /* Read 0-14 bits to get length of received packet, manual pg 4081, table 11-152, RDES3 Normal Descriptor */
            net_buff_desc_t buffer = { (uint64_t)d->addr_low | ((uint64_t d->addr_high) << 32), d->des3 & 0x7FFF };
            int err = net_enqueue_active(&rx_queue, buffer);
            assert(!err);
            packets_transferred = true;
        }
        rx.head++;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(config.virt_rx.id);
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

            // For normal transmit descriptors, tdes2 needs to be set to generate an IRQ on transmit
            // completion. We also need to provide the length of the buffer data in bits 13:0.
            uint32_t des2 = DESC_TXCTRL_TXINT | buffer.len;

            uint32_t idx = tx.tail % tx.capacity;
            // For normal transmit descriptors, we need to give ownership to DMA, as well as indicate
            // that this is the first and last parts of the current packet.
            uint32_t des3 = (DESC_TXSTS_OWNBYDMA | DESC_TXCTRL_TXFIRST | DESC_TXCTRL_TXLAST | DESC_TXCTRL_TXCIC
                             | buffer.len);

            update_ring_slot(&tx, idx, buffer.io_or_offset & 0xffffffff, buffer.io_or_offset >> 32, des2, des3);

            tx.tail++;
            /* Set the tail in hardware to the latest tail we have inserted in.
             * This tells the hardware that it has new buffers to send.
             * NOTE: Setting this on every enqueued packet for sanity, change this to once per batch.
             */
            *DMA_REG(DMA_CH0_TXDESC_TAIL_PTR) = tx_desc_base + sizeof(struct descriptor) * (idx);
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
        if (d->des3 & DESC_TXSTS_OWNBYDMA) {
            break;
        }
        THREAD_MEMORY_ACQUIRE();

        net_buff_desc_t buffer = { (uint64_t)d->addr_low | ((uint64_t d->addr_high) << 32), 0 };
        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);
        enqueued = true;
        tx.head++;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(config.virt_tx.id);
    }
}

static void handle_irq()
{
    uint32_t e = *DMA_REG(DMA_CH0_STATUS);
    *DMA_REG(DMA_CH0_STATUS) &= e;

    while (e & DMA_INTR_MASK) {
        if (e & DMA_CH0_INTERRUPT_EN_RIE) {
            rx_return();
        }
        if (e & DMA_CH0_INTERRUPT_EN_TIE) {
            tx_return();
            tx_provide();
        }
        if (e & DMA_INTR_ABNORMAL) {
            if (e & DMA_CH0_INTERRUPT_EN_FBEE) {
                sddf_dprintf("Ethernet device fatal bus error\n");
            }
        }
        e = *DMA_REG(DMA_CH0_STATUS);
        *DMA_REG(DMA_CH0_STATUS) &= e;
    }
}

static void eth_init()
{
    // Software reset -- This will reset the MAC internal registers.
    volatile uint32_t *mode = DMA_REG(DMA_MODE);
    *mode |= DMA_MODE_SWR;

    // Poll on BIT 0. This bit is cleared by the device when the reset is complete.
    while (1) {
        mode = DMA_REG(DMA_MODE);
        if (!(*mode & DMA_MODE_SWR)) {
            break;
        }
    }

    /* Configure MTL */

    // Enable store and forward mode for TX, and enable the TX queue.
    *MTL_REG(MTL_TXQ0_OPERATION_MODE) |= MTL_TXQ_OP_MODE_TSF | MTL_TXQ_OP_MODE_TXQEN;

    // Enable store and forward mode for rx
    *MTL_REG(MTL_RXQ0_OPERATION_MODE) |= MTL_RXQ_OP_MODE_RSF;

    // Program the rx queue to the DMA mapping.
    uint32_t map0 = *MTL_REG(MTL_RXQ_DMA_MAP0);
    // We only have one queue, and we map it onto DMA channel 0
    map0 &= ~MTL_RXQ_DMA_MAP0_Q0_MDMACH_MASK;
    map0 |= MTL_RXQ_DMA_MAP0_Q0_DMA0;
    *MTL_REG(MTL_RXQ_DMA_MAP0) = map0;

    // Transmit/receive queue fifo size, use all RAM for 1 queue
    uint32_t val = *MAC_REG(MAC_HW_FEATURE1);
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

    *MTL_REG(MTL_TXQ0_OPERATION_MODE) &= ~(MTL_TXQ_OP_MODE_TQS_MASK);
    *MTL_REG(MTL_TXQ0_OPERATION_MODE) |= tqs << MTL_TXQ_OP_MODE_TQS_POS;
    *MTL_REG(MTL_RXQ0_OPERATION_MODE) &= ~(MTL_RXQ_OP_MODE_RQS_MASK);
    *MTL_REG(MTL_RXQ0_OPERATION_MODE) |= rqs << MTL_RXQ_OP_MODE_RQS_POS;

    // NOTE - more stuff in dwc_eth_qos that we are skipping regarding to tuning the tqs

    /* Configure MAC */
    *MAC_REG(MAC_RXQ_CTRL0) &= MAC_RXQ_CTRL0_Q0_CLEAR;
    *MAC_REG(MAC_RXQ_CTRL0) |= MAC_RXQ_CTRL0_Q0_DCB_GEN_EN;

    uint32_t filter = MAC_PACKET_FILTER_PR;

    *MAC_REG(MAC_PACKET_FILTER) = filter;

    // For now, disabling all flow control.

    *MAC_REG(MAC_Q0_TX_FLOW_CTRL) = 0;

    // Program all other appropriate fields in MAC_CONFIGURATION
    //       (ie. inter-packet gap, jabber disable).
    uint32_t conf = *MAC_REG(MAC_CONFIGURATION);
    // Set full duplex mode
    conf |= MAC_CONFIG_DM;
    // Enable checksum offload
    conf |= MAC_CONFIG_IPC;

    // Setting the speed of our device to 1000mbps
    conf &= ~(MAC_CONFIG_PS | MAC_CONFIG_FES);
    *MAC_REG(MAC_CONFIGURATION) = conf;

    // Set the MAC Address.

    /* NOTE: We are hardcoding this MAC address to the hardware MAC address of the
    Star64 in the TS machine queue. This address is resident the boards EEPROM, however,
    we need I2C to read from this ROM. */
    *MAC_REG(MAC_ADDRESS0_HIGH) = 0x00005b75;
    *MAC_REG(MAC_ADDRESS0_LOW) = 0x0039cf6c;

    /* Configure DMA */

    // Enable operate on second packet
    *DMA_REG(DMA_CH0_TX_CONTROL) |= DMA_CH0_TX_CONTROL_OSF;

    // Set the max packet size for rx
    *DMA_REG(DMA_CH0_RX_CONTROL) &= ~(DMA_CH0_RX_RBSZ_MASK);
    *DMA_REG(DMA_CH0_RX_CONTROL) |= (MAX_RX_FRAME_SZ << DMA_CH0_RX_RBSZ_POS);

    // Program the descriptor length. This is to tell the device that when
    // we reach the base addr + count, we should then wrap back around to
    // the base.

    *DMA_REG(DMA_CH0_TXDESC_RING_LENGTH) = TX_COUNT - 1;
    *DMA_REG(DMA_CH0_RXDESC_RING_LENGTH) = RX_COUNT - 1;

    // Init rx and tx descriptor list addresses.
    rx_desc_base = device_resources.regions[1].io_addr;
    tx_desc_base = device_resources.regions[2].io_addr;

    *DMA_REG(DMA_CH0_RXDESC_LIST_ADDR) = rx_desc_base & 0xffffffff;
    *DMA_REG(DMA_CH0_TXDESC_LIST_ADDR) = tx_desc_base & 0xffffffff;

    // Enable interrupts.
    *DMA_REG(DMA_CH0_INTERRUPT_EN) = DMA_INTR_NORMAL;

    // Populate the rx and tx hardware rings.
    rx_provide();
    tx_provide();

    // Start DMA and MAC
    *DMA_REG(DMA_CH0_TX_CONTROL) |= DMA_CH0_TX_CONTROL_ST;
    *DMA_REG(DMA_CH0_RX_CONTROL) |= DMA_CH0_RX_CONTROL_SR;
    *MAC_REG(MAC_CONFIGURATION) |= (MAC_CONFIG_RE | MAC_CONFIG_TE);

    /* NOTE ------ FROM U-BOOT SOURCE CODE dwc_eth_qos.c:995 */

    /* TX tail pointer not written until we need to TX a packet */
    /*
	 * Point RX tail pointer at last descriptor. Ideally, we'd point at the
	 * first descriptor, implying all descriptors were available. However,
	 * that's not distinguishable from none of the descriptors being
	 * available.
	 */
    *DMA_REG(DMA_CH0_RXDESC_TAIL_PTR) = rx_desc_base + (sizeof(struct descriptor) * (RX_COUNT - 1));
}

static void eth_setup(void)
{
    assert((device_resources.regions[1].io_addr & 0xFFFFFFFF) == device_resources.regions[1].io_addr);

    rx.capacity = RX_COUNT;
    rx.descr = (volatile struct descriptor *)device_resources.regions[1].region.vaddr;
    tx.capacity = TX_COUNT;
    tx.descr = (volatile struct descriptor *)device_resources.regions[2].region.vaddr;

    eth_init();
}

void init(void)
{
    assert(net_config_check_magic((void *)&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 3);
    // All buffers should fit within our DMA region
    assert(RX_COUNT * sizeof(struct descriptor) <= device_resources.regions[1].region.size);
    assert(TX_COUNT * sizeof(struct descriptor) <= device_resources.regions[2].region.size);

    eth_regs = (void *)device_resources.regions[0].region.vaddr;

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
    uint32_t phy_stat = *MAC_REG(MAC_PHYIF_CONTROL_STATUS);
    if (phy_stat & MAC_PHYIF_CONTROL_LINKSTS) {
        sddf_dprintf("PHY device is up and running\n");
    } else {
        sddf_dprintf("PHY device is currently down\n");
    }

    if (phy_stat & BIT(16)) {
        sddf_dprintf("PHY device is operating in full duplex mode\n");
    } else {
        sddf_dprintf("PHY device is operating in half duplex mode\n");
    }

    net_queue_init(&rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);
    eth_setup();

    microkit_irq_ack(device_resources.irqs[0].id);
}

void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        microkit_deferred_irq_ack(ch);
    } else if (ch == config.virt_rx.id) {
        rx_provide();
    } else if (ch == config.virt_tx.id) {
        tx_provide();
    } else {
        sddf_dprintf("ETH|LOG: received notification on unexpected channel %u\n", ch);
    }
}
