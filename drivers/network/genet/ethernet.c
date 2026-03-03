/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * This driver is based on the Linux driver:
 *      drivers/net/ethernet/broadcom/genet/bcmgenet.c
 *      which is: Copyright (c) 2014-2017 Broadcom
 *
 * Also referred to:
 *      https://github.com/u-boot/u-boot/blob/master/drivers/net/bcmgenet.c
 *      https://github.com/RT-Thread/rt-thread/blob/master/bsp/raspberry-pi/raspi4-32/driver/drv_eth.c
 *      BCM54213PE Datasheet
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/network/constants.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#include "ethernet.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".net_driver_config"))) net_driver_config_t config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

volatile struct genet_regs *eth;
volatile struct mbox_regs *mbox_regs;
volatile uint32_t *mbox;

volatile struct genet_dma_ring_rx *ring_rx;
volatile struct genet_dma_ring_tx *ring_tx;

/* HW ring buffer data type */
typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of description ring */
    uint32_t desc_id_mask; /* mask of description id */
    uint32_t index_mask; /* mask of index in ring */
    volatile struct genet_dma_desc *descr; /* buffer descriptor array */
} hw_ring_t;

hw_ring_t rx;
hw_ring_t tx;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

static inline bool hw_ring_full(hw_ring_t *ring)
{
    return ring->tail - ring->head == ring->capacity;
}

static inline bool hw_ring_empty(hw_ring_t *ring)
{
    return ring->tail - ring->head == 0;
}

static void update_ring_slot(hw_ring_t *ring, unsigned int idx, uintptr_t phys, uint32_t stat)
{
    volatile struct genet_dma_desc *d = &(ring->descr[idx]);
    d->addr_lo = phys & 0xFFFFFFFF;
    d->addr_hi = phys >> 32;
    d->status = stat;

    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    THREAD_MEMORY_RELEASE();
}

static void sleep_us(uint32_t us)
{
    uint64_t start = sddf_timer_time_now(timer_config.driver_id);
    while ((sddf_timer_time_now(timer_config.driver_id) - start) < us * NS_IN_US);
}

static void bcmgenet_mdio_write(uint8_t reg_addr, uint16_t val)
{
    uint32_t cmd = MDIO_WR | (GENET_PHY_ID << MDIO_PMD_SHIFT) | ((reg_addr & MDIO_REG_MASK) << MDIO_REG_SHIFT) | val;
    eth->umac_mdio_cmd = cmd;

    uint32_t reg = eth->umac_mdio_cmd | MDIO_START_BUSY;
    eth->umac_mdio_cmd = reg;

    while (eth->umac_mdio_cmd & MDIO_START_BUSY);
}

static uint16_t bcmgenet_mdio_read(uint8_t reg_addr)
{
    uint32_t cmd = MDIO_RD | (GENET_PHY_ID << MDIO_PMD_SHIFT) | ((reg_addr & MDIO_REG_MASK) << MDIO_REG_SHIFT);
    eth->umac_mdio_cmd = cmd;

    uint32_t reg = eth->umac_mdio_cmd | MDIO_START_BUSY;
    eth->umac_mdio_cmd = reg;

    while (eth->umac_mdio_cmd & MDIO_START_BUSY);

    return eth->umac_mdio_cmd & 0xFFFF;
}

static void rx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&rx) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint32_t idx = rx.tail & rx.desc_id_mask;
            update_ring_slot(&rx, idx, buffer.io_or_offset, 0);
            rx.tail++;
        }
        // Doorbell the device
        ring_rx->cons_index = (rx.tail - NUM_DESCS) & rx.index_mask;

        // Only request a notification from virtualiser if HW ring not full
        if (!hw_ring_full(&rx)) {
            net_request_signal_free(&rx_queue);
        } else {
            net_cancel_signal_free(&rx_queue);
        }
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

    // Each register read takes over 300 cycles, so we read prod_index once
    // for optimisation. The packets arrived before clearing IRQ status will
    // be handled in next iteration.
    uint32_t prod_index = ring_rx->prod_index & rx.index_mask;
    while (!hw_ring_empty(&rx)) {
        if ((rx.head & rx.index_mask) == prod_index) {
            break;
        }
        uint32_t idx = rx.head & rx.desc_id_mask;
        volatile struct genet_dma_desc *d = &(rx.descr[idx]);

        THREAD_MEMORY_ACQUIRE();

        uint64_t addr = ((uint64_t)(d->addr_hi) << 32) | d->addr_lo;
        net_buff_desc_t buffer = { addr, d->status >> DMA_BUFLENGTH_SHIFT };
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        packets_transferred = true;
        rx.head++;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        sddf_notify(config.virt_rx.id);
    }
}

static void tx_provide()
{
    bool reprocess = true;
    while (reprocess) {
        while (!(hw_ring_full(&tx)) && !net_queue_empty_active(&tx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            uint32_t idx = tx.tail & tx.desc_id_mask;
            uint32_t stat = (buffer.len << DMA_BUFLENGTH_SHIFT) | (0x3F << DMA_TX_QTAG_SHIFT) | DMA_TX_APPEND_CRC
                          | DMA_TX_DO_CSUM | DMA_SOP | DMA_EOP;
            update_ring_slot(&tx, idx, buffer.io_or_offset, stat);

            tx.tail++;
        }
        ring_tx->prod_index = tx.tail & tx.index_mask;

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
    uint32_t cons_index = ring_tx->cons_index & tx.index_mask;
    while (!hw_ring_empty(&tx)) {
        if ((tx.head & tx.index_mask) == cons_index) {
            break;
        }
        uint32_t idx = tx.head & tx.desc_id_mask;
        volatile struct genet_dma_desc *d = &(tx.descr[idx]);

        THREAD_MEMORY_ACQUIRE();

        uint64_t addr = ((uint64_t)(d->addr_hi) << 32) | d->addr_lo;
        net_buff_desc_t buffer = { addr, 0 };
        int err = net_enqueue_free(&tx_queue, buffer);
        assert(!err);

        enqueued = true;
        tx.head++;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        sddf_notify(config.virt_tx.id);
    }
}

static void handle_irq(void)
{
    uint32_t irq_status = eth->intrl2_0_cpu_stat & ~(eth->intrl2_0_cpu_stat_mask);
    eth->intrl2_0_cpu_clear = irq_status;
    while (irq_status) {
        if (irq_status & GENET_IRQ_TXDMA_DONE) {
            tx_return();
            tx_provide();
        }
        if (irq_status & GENET_IRQ_RXDMA_DONE) {
            rx_return();
            rx_provide();
        }
        irq_status = eth->intrl2_0_cpu_stat & ~(eth->intrl2_0_cpu_stat_mask);
        eth->intrl2_0_cpu_clear = irq_status;
    }
}

static void eth_setup(void)
{
    eth = device_resources.regions[0].region.vaddr;

    uint8_t version_major = (eth->sys_rev_ctrl >> 24) & 0x0f;
    if (version_major != 6) {
        sddf_dprintf("Unsupported GENET version\n");
    }

    // Set PHY interface
    eth->sys_port_ctrl = PORT_MODE_EXT_GPHY;

    // Rbuf clear
    eth->sys_rbuf_flush_ctrl = 0;

    // Disable MAC while updating its registers
    eth->umac_cmd = 0;
    // issue soft reset with (rg)mii loopback to ensure a stable rxclk
    eth->umac_cmd = CMD_SW_RESET | CMD_LCL_LOOP_EN;

    // MDIO init
    uint32_t uid_high = bcmgenet_mdio_read(BCM54213PE_PHY_IDENTIFIER_HIGH);
    uint32_t uid_low = bcmgenet_mdio_read(BCM54213PE_PHY_IDENTIFIER_LOW);
    if (((uid_high << 16) | (uid_low & 0xFFFF)) == 0) {
        sddf_dprintf("ERROR: invalid ethernet UID '0'\n");
        return;
    }

    // reset phy
    bcmgenet_mdio_write(BCM54213PE_MII_CONTROL, MII_CONTROL_PHY_RESET);
    // read control reg
    bcmgenet_mdio_read(BCM54213PE_MII_CONTROL);
    // reset phy again
    bcmgenet_mdio_write(BCM54213PE_MII_CONTROL, MII_CONTROL_PHY_RESET);
    // read control reg
    bcmgenet_mdio_read(BCM54213PE_MII_CONTROL);
    // read status reg
    bcmgenet_mdio_read(BCM54213PE_MII_STATUS);
    // read status reg
    bcmgenet_mdio_read(BCM54213PE_IEEE_EXTENDED_STATUS);
    bcmgenet_mdio_read(BCM54213PE_AUTO_NEGOTIATION_ADV);

    bcmgenet_mdio_read(BCM54213PE_MII_STATUS);
    bcmgenet_mdio_read(BCM54213PE_CONTROL);
    // half full duplex capability
    bcmgenet_mdio_write(BCM54213PE_CONTROL, (CONTROL_HALF_DUPLEX_CAPABILITY | CONTROL_FULL_DUPLEX_CAPABILITY));
    bcmgenet_mdio_read(BCM54213PE_MII_CONTROL);

    // set mii control
    bcmgenet_mdio_write(BCM54213PE_MII_CONTROL,
                        (MII_CONTROL_AUTO_NEGOTIATION_ENABLED | MII_CONTROL_AUTO_NEGOTIATION_RESTART
                         | MII_CONTROL_PHY_FULL_DUPLEX | MII_CONTROL_SPEED_SELECTION));

    while (~bcmgenet_mdio_read(BCM54213PE_MII_STATUS) & MII_STATUS_AUTO_NEGOTIATION_COMPLETE);

    // Set MAC address
    mbox[0] = 8 * 4;                                 // length of the message
    mbox[1] = MBOX_REQUEST;                        // this is a request message
    mbox[2] = MBOX_TAG_HARDWARE_GET_MAC_ADDRESS;
    mbox[3] = 6;                                   // buffer size
    mbox[4] = 0;                                   // len
    mbox[5] = 0;
    mbox[6] = 0;
    mbox[7] = MBOX_TAG_LAST;

    // 0x8 is the channel identifier for Property Tags
    unsigned int r = device_resources.regions[3].io_addr | 0x8;
    /* wait until we can write to the mailbox */
    while (mbox_regs->status & MBOX_FULL);
    // write the address of our message to the mailbox with channel identifier
    mbox_regs->write = r;
    // wait for the response
    while (1) {
        // check if response is ready
        while (mbox_regs->status & MBOX_EMPTY);
        // check if response is for us
        if (r == mbox_regs->read) {
            if (mbox[1] != MBOX_RESPONSE) {
                sddf_dprintf("ERROR: Invalid mbox response\n");
                return;
            }
            break;
        }
    }
    char *mac = (char *)&mbox[5];
    eth->umac_mac0 = mac[0] << 24 | mac[1] << 16 | mac[2] << 8 | mac[3];
    eth->umac_mac1 = mac[4] << 8 | mac[5];

    // UMAC Reset
    eth->sys_rbuf_flush_ctrl |= BIT(1);
    eth->sys_rbuf_flush_ctrl &= ~BIT(1);
    sleep_us(10);

    eth->sys_rbuf_flush_ctrl = 0;
    sleep_us(10);

    eth->umac_cmd = 0;
    eth->umac_cmd = CMD_SW_RESET | CMD_LCL_LOOP_EN;
    sleep_us(2);

    eth->umac_cmd = 0;
    eth->umac_mib_ctrl = MIB_RESET_RX | MIB_RESET_TX | MIB_RESET_RUNT;
    eth->umac_mib_ctrl = 0;
    eth->umac_max_frame_len = ENET_MAX_MTU_SIZE;

    // Disable this bit to not pad two bytes at the beginning of every packet
    eth->rbuf_ctrl &= ~RBUF_ALIGN_2B;
    eth->rbuf_tbuf_size_ctrl = 1;

    // Disable DMA
    eth->dma_tx.ctrl &= ~BIT(DMA_EN);
    eth->dma_rx.ctrl &= ~BIT(DMA_EN);
    eth->umac_tx_flush = 1;
    sleep_us(100);
    eth->umac_tx_flush = 0;

    // Rx Ring Init
    ring_rx = (struct genet_dma_ring_rx *)&eth->dma_rx.ring;
    eth->dma_rx.burst_size = DMA_MAX_BURST_LENGTH;
    ring_rx->start_addr = 0;
    ring_rx->read_ptr = 0;
    ring_rx->write_ptr = 0;
    ring_rx->end_addr = NUM_DESCS * DESC_SIZE / 4 - 1;
    ring_rx->prod_index = 0;
    ring_rx->cons_index = 0;
    ring_rx->buf_size = (NUM_DESCS << 16) | NET_BUFFER_SIZE;
    ring_rx->mbuf_done_thresh = 0x1;
    ring_rx->xon_xoff_thresh = (NUM_DESCS >> 4) | (5 << 16);
    // We only use the default ring (i.e. ring 16)
    eth->dma_rx.ring_cfg = BIT(DEFAULT_Q);
    eth->rbuf_ctrl |= RBUF_64B_EN;

    // Tx Ring Init
    ring_tx = (struct genet_dma_ring_tx *)&eth->dma_tx.ring;
    eth->dma_tx.burst_size = DMA_MAX_BURST_LENGTH;
    ring_tx->start_addr = 0;
    ring_tx->read_ptr = 0;
    ring_tx->write_ptr = 0;
    ring_tx->prod_index = ring_tx->cons_index;
    ring_tx->end_addr = NUM_DESCS * DESC_SIZE / 4 - 1;
    ring_tx->mbuf_done_thresh = 0x80;
    ring_tx->flow_period = 0;
    ring_tx->buf_size = (NUM_DESCS << 16) | NET_BUFFER_SIZE;
    eth->dma_tx.ring_cfg = BIT(DEFAULT_Q);
    eth->tbuf_ctrl |= TBUF_64B_EN;
    // No timeout for Tx Coalescing but IRQs generated after mbuf_done_thresh or empty buffer

    // Enable DMA
    uint32_t dma_ctrl = (1 << (DEFAULT_Q + DMA_RING_BUF_EN_SHIFT)) | DMA_EN;
    eth->dma_tx.ctrl = dma_ctrl;
    eth->dma_rx.ctrl |= dma_ctrl;

    // Adjust Link
    uint32_t oob_ctrl = eth->ext_rgmii_oob_ctrl | RGMII_LINK | RGMII_MODE_EN | ID_MODE_DIS;
    eth->ext_rgmii_oob_ctrl = oob_ctrl;
    sleep_us(1000);
    eth->umac_cmd = UMAC_SPEED_1000 << CMD_SPEED_SHIFT;

    // Index Reset
    tx.descr = (struct genet_dma_desc *)&eth->dma_tx.descs;
    tx.head = ring_tx->cons_index;
    tx.tail = ring_tx->prod_index;
    tx.capacity = NUM_DESCS;
    tx.desc_id_mask = NUM_DESCS - 1;
    tx.index_mask = 0xFFFF;

    rx.head = ring_rx->prod_index;
    rx.tail = rx.head;
    rx.capacity = NUM_DESCS;
    rx.desc_id_mask = NUM_DESCS - 1;
    rx.index_mask = 0xFFFF;
    rx.descr = (struct genet_dma_desc *)&eth->dma_rx.descs;

    // Fill empty buffers for Rx
    rx_provide();

    ring_rx->cons_index = rx.head;
    ring_rx->prod_index = rx.head;

    // Enable promisc mode
    eth->umac_cmd = eth->umac_cmd | CMD_PROMISC;
    eth->umac_mdf_ctrl = 0;

    // Enable Rx/Tx
    eth->umac_cmd |= (CMD_TX_EN | CMD_RX_EN);

    // Clear IRQ status
    uint32_t irq_status = eth->intrl2_0_cpu_stat & ~(eth->intrl2_1_cpu_stat_mask);
    eth->intrl2_0_cpu_clear = irq_status;

    // Enable IRQ
    eth->intrl2_0_cpu_clear_mask = GENET_IRQ_TXDMA_DONE | GENET_IRQ_RXDMA_DONE;
}

uint32_t rpi4_get_cpu_frequency()
{
    mbox[0] = 8 * 4;                                 // Length of the message
    mbox[1] = MBOX_REQUEST;                        // Request code
    mbox[2] = MBOX_TAG_HARDWARE_GET_CLK_RATE;      // tag
    mbox[3] = 8;                                   // Buffer size
    mbox[4] = 0;                                   // Response size
    mbox[5] = 0x00000003;                          // Clock ID: ARM
    mbox[6] = MBOX_TAG_LAST;                       // End tag

    // 0x8 is the channel identifier for Property Tags
    unsigned int r = device_resources.regions[3].io_addr | 0x8;
    /* wait until we can write to the mailbox */
    while (mbox_regs->status & MBOX_FULL);
    // write the address of our message to the mailbox with channel identifier
    mbox_regs->write = r;
    // wait for the response
    while (1) {
        // check if response is ready
        while (mbox_regs->status & MBOX_EMPTY);
        // check if response is for us
        if (r == mbox_regs->read) {
            if (mbox[1] != MBOX_RESPONSE) {
                return 0;
            }
            break;
        }
    }

    uint32_t *cpu_freq = (uint32_t *)&mbox[6];
    return *cpu_freq;
}

void rpi4_set_cpu_frequency(uint32_t freq)
{
    mbox[0] = 8 * 4;                                 // Length of the message
    mbox[1] = MBOX_REQUEST;                        // Request code
    mbox[2] = MBOX_TAG_HARDWARE_SET_CLK_RATE;      // tag
    mbox[3] = 12;                                  // Buffer size
    mbox[4] = 8;                                   // Response size
    mbox[5] = 0x00000003;                          // Clock ID: ARM
    mbox[6] = freq;                                // Frequency in Hz
    mbox[7] = MBOX_TAG_LAST;                       // End tag

    // 0x8 is the channel identifier for Property Tags
    unsigned int r = device_resources.regions[3].io_addr | 0x8;
    /* wait until we can write to the mailbox */
    while (mbox_regs->status & MBOX_FULL);
    // write the address of our message to the mailbox with channel identifier
    mbox_regs->write = r;
    // wait for the response
    while (1) {
        // check if response is ready
        while (mbox_regs->status & MBOX_EMPTY);
        // check if response is for us
        if (r == mbox_regs->read) {
            if (mbox[1] != MBOX_RESPONSE) {
                return;
            }
            break;
        }
    }
}

void init(void)
{
    mbox_regs = (struct mbox_regs *)0x3000880;
    mbox = device_resources.regions[3].region.vaddr;

    net_queue_init(&rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    rpi4_set_cpu_frequency(1000000000);

    eth_setup();

    tx_provide();
}

void notified(sddf_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();

        sddf_deferred_irq_ack(ch);
    } else if (ch == config.virt_rx.id) {
        rx_provide();
    } else if (ch == config.virt_tx.id) {
        tx_provide();
    } else {
        sddf_dprintf("ETH|LOG: received notification on unexpected channel: %u\n", ch);
    }
}
