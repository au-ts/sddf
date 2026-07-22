/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Intel Ethernet Controller X550 Datasheet:
 *   https://cdrdv2-public.intel.com/333369/333369_X550_Datasheet_Rev2.7.pdf
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/network/queue.h>
#include <sddf/network/config.h>
#include <sddf/util/util.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#include "ethernet.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".net_driver_config"))) net_driver_config_t config;

#define RX_IRQ_VECTOR 0
#define TX_IRQ_VECTOR 1

// Minimum inter-interrupt interval specified in 2.048 us units
// at 1 GbE and 10 GbE link
#define IRQ_INTERVAL 40

const uint64_t hw_rx_ring_paddr = 0x10000000;
const uint64_t hw_rx_ring_vaddr = 0x2400000;
const uint64_t hw_tx_ring_paddr = 0x10004000;
const uint64_t hw_tx_ring_vaddr = 0x2404000;

#define NUM_TX_DESCS 512llu
#define NUM_RX_DESCS 512llu
#define TX_CLEAN_BATCH 32llu

struct ixgbe_device {
    volatile ixgbe_adv_rx_desc_t *rx_ring;
    uint32_t rx_head, rx_tail;
    volatile ixgbe_adv_tx_desc_t *tx_ring;
    uint32_t tx_head, tx_tail;
    net_buff_desc_t rx_descr_mdata[NUM_RX_DESCS];
    net_buff_desc_t tx_descr_mdata[NUM_TX_DESCS];
    int init_stage;
} device;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

#define MAX_PACKET_SIZE     1536

volatile eth_regs_t *eth_regs;

static inline bool hw_tx_ring_empty(void)
{
    return device.tx_head == device.tx_tail;
}

static inline bool hw_tx_ring_full(void)
{
    return (device.tx_tail + 1) % NUM_TX_DESCS == device.tx_head;
}

static inline bool hw_rx_ring_empty(void)
{
    return device.rx_head == device.rx_tail;
}

static inline bool hw_rx_ring_full(void)
{
    return (device.rx_tail + 1) % NUM_RX_DESCS == device.rx_head;
}

void clear_interrupts(void)
{
    (void)eth_regs->eicr;
}

void disable_interrupts(void)
{
    eth_regs->eimc = IXGBE_IRQ_CLEAR_MASK;
    clear_interrupts();
}

void enable_interrupts(void)
{
    // Section 8.2.2.6.10
    //   - Bit[5:0] vector number for RX_QUEUE 0, BIT(vector number) is set on EICR if triggered
    //   - Bit[7] enable IRQ for RX_QUEUE 0
    //   - Bit[13:8] vector number for TX_QUEUE 0
    //   - Bit[15] enable IRQ for TX_QUEUE 0
    eth_regs->ivar[0] = RX_IRQ_VECTOR | BIT(7) | (TX_IRQ_VECTOR << 8) | BIT(15);

    // Section 7.3.1.6 - No need to enable auto-clear
    eth_regs->eiac = 0;

    // Section 8.2.2.6.4
    //   - Bits[11:3] Minimum inter-interrupt interval specified in 2.048us units
    //   at 1 GbE and 10 GbE link
    eth_regs->eitr[0] = IXGBE_EITR_ITR_INTERVAL * IRQ_INTERVAL;
    clear_interrupts();

    // Section 8.2.2.6.1
    //   - Bit[15:0] for Receive/Transmit Queue Interrupts. We only enable those IRQs
    //   because the driver doesn't know how to handle IRQs caused by other reasons.
    eth_regs->eims = 0xFF;
}

void get_mac_addr(uint8_t mac[6])
{
    uint64_t low = eth_regs->rx_addr[0].lo;
    uint64_t high = eth_regs->rx_addr[0].hi;

    mac[0] = low & 0xff;
    mac[1] = low >> 8 & 0xff;
    mac[2] = low >> 16 & 0xff;
    mac[3] = low >> 24;
    mac[4] = high & 0xff;
    mac[5] = high >> 8 & 0xff;
}

uint32_t get_link_speed(void)
{
    uint32_t speed = eth_regs->links;
    if ((speed & IXGBE_LINKS_UP) == 0) {
        return 0;
    }
    switch (speed & IXGBE_LINKS_SPEED_82599) {
    case IXGBE_LINKS_SPEED_100_82599:
        return 100;
    case IXGBE_LINKS_SPEED_1G_82599:
        return 1000;
    case IXGBE_LINKS_SPEED_10G_82599:
        return 10000;
    default:
        return 0;
    }
}

void rx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        bool provided = false;

        while (!hw_rx_ring_full() && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            volatile ixgbe_adv_rx_desc_t *desc = &device.rx_ring[device.rx_tail];
            desc->read.pkt_addr = buffer.io_or_offset;
            desc->read.hdr_addr = 0;

            // Section 7.1.5.2.2 - We need a local copy becasue RX descriptor
            // does not contain the address at write-back phase.
            device.rx_descr_mdata[device.rx_tail] = buffer;

            device.rx_tail = (device.rx_tail + 1) % NUM_RX_DESCS;
            provided = true;
        }

        if (provided) {
            THREAD_MEMORY_RELEASE();
            eth_regs->rx_dma[0].rdt = device.rx_tail;
        }

        /* Only request a notification from multiplexer if HW ring is empty */
        if (!hw_rx_ring_full()) {
            net_request_signal_free(&rx_queue);
        } else {
            net_cancel_signal_free(&rx_queue);
        }
        reprocess = false;

        if (!net_queue_empty_free(&rx_queue) && !hw_rx_ring_full()) {
            net_cancel_signal_free(&rx_queue);
            reprocess = true;
        }
    }
}

static void rx_return(void)
{
    bool packets_transferred = false;
    while (!hw_rx_ring_empty()) {
        ixgbe_adv_rx_desc_wb_t desc = device.rx_ring[device.rx_head].wb;
        if ((desc.upper.status_error & IXGBE_RXDADV_STAT_DD) == 0) {
            // The desciptor hasn't been used by hardware, implying no more available packets received
            break;
        }
        if ((desc.upper.status_error & IXGBE_RXDADV_STAT_EOP) == 0) {
            // See Table 7-16: DD=1 and EOP=0
            sddf_dprintf("ETH|ERROR: The packet spans across multiple descriptors.\n");
            break;
        }

        // The access to `status_error` field should be ordered before the access to the `length` field
        THREAD_MEMORY_ACQUIRE();

        net_buff_desc_t buffer = device.rx_descr_mdata[device.rx_head];
        buffer.len = desc.upper.length;
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        packets_transferred = true;
        device.rx_head = (device.rx_head + 1) % NUM_RX_DESCS;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        microkit_notify(config.virt_rx.id);
    }
}

void tx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        bool provided = false;

        while (!(hw_tx_ring_full()) && !net_queue_empty_active(&tx_queue)) {

            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            volatile ixgbe_adv_tx_desc_t *desc = &device.tx_ring[device.tx_tail];
            desc->read.buffer_addr = buffer.io_or_offset;
            desc->read.cmd_type_len = IXGBE_ADVTXD_DCMD_EOP | IXGBE_ADVTXD_DCMD_RS | IXGBE_ADVTXD_DCMD_IFCS
                                    | IXGBE_ADVTXD_DCMD_DEXT | IXGBE_ADVTXD_DTYP_DATA | (uint32_t)buffer.len;
            desc->read.olinfo_status = ((uint32_t)buffer.len << IXGBE_ADVTXD_PAYLEN_SHIFT);

            // Section 7.2.3.2.3 - same reason with Rx descriptors to have a local copy
            device.tx_descr_mdata[device.tx_tail] = buffer;

            device.tx_tail = (device.tx_tail + 1) % NUM_TX_DESCS;
            provided = true;
        }

        if (provided) {
            THREAD_MEMORY_RELEASE();
            eth_regs->tx_dma[0].tdt = device.tx_tail;
            eth_regs->tx_dma[0].tdt; // Write flush
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        if (!hw_tx_ring_full() && !net_queue_empty_active(&tx_queue)) {
            net_cancel_signal_active(&tx_queue);
            reprocess = true;
        }
    }
}

void tx_return(void)
{
    bool enqueued = false;
    while (!hw_tx_ring_empty()) {
        /* Ensure that this buffer has been sent by the device */
        ixgbe_adv_tx_desc_wb_t hw_desc = device.tx_ring[device.tx_head].wb;

        if ((hw_desc.status & IXGBE_ADVTXD_STAT_DD) == 0)
            break;

        net_buff_desc_t descr_mdata = device.tx_descr_mdata[device.tx_head];
        int err = net_enqueue_free(&tx_queue, descr_mdata);
        assert(!err);
        enqueued = true;

        device.tx_head = (device.tx_head + 1) % NUM_TX_DESCS;
    }

    if (enqueued && net_require_signal_free(&tx_queue)) {
        net_cancel_signal_free(&tx_queue);
        microkit_notify(config.virt_tx.id);
    }
}

void init(void)
{
    eth_regs = (eth_regs_t *)0x2000000;

    // see PCI Express Technology 3.0 Chapter 17 for more details.
    // =====Uncomment the below code snippet to use MSI interrupts========
    /* set_flags16(PCI_COMMAND_16, BIT(10)); */
    /* set_flags16(PCI_MSI_MESSAGE_CONTROL_16, BIT(0)); */
    /* clear_flags16(PCI_MSI_MESSAGE_CONTROL_16, BIT(4) | BIT(5) | BIT(6)); */
    /* set_reg(PCI_MSI_MESSAGE_ADDRESS_LOW, 0xFEEu << 20); */
    /* set_reg(PCI_MSI_MESSAGE_ADDRESS_HIGH, 0); */
    /* set_reg16(PCI_MSI_MESSAGE_DATA_16, 0x31); */
    /* clear_flags16(PCI_MSI_MASK, BIT(0)); */

    // see PCI Express Technology 3.0 Chapter 17 for more details.
    // =====Uncomment the below code snippet to use MSI-X interrupts======
    /* // Disable legacy interrupts. */
    /* set_flags16(PCI_COMMAND_16, BIT(10)); */
    /* // Set vector message address to Local APIC of CPU0 */
    /* set_reg(DEVICE_MSIX_TABLE + 0x0, 0xFEEu << 20); */
    /* set_reg(DEVICE_MSIX_TABLE + 0x4, 0); */
    /* // Set vector data to Interrupt Vector */
    /* set_reg(DEVICE_MSIX_TABLE + 0x8, 0x32); */
    /* // Unmask vector 0 to enable interrupts through it */
    /* set_reg(DEVICE_MSIX_TABLE + 0xC, 0xFFFFFFFE); */
    /* // Enable MSI-X. */
    /* set_flags(PCI_MSIX_CTRL, BIT(31)); */

    device.rx_ring = (void *)hw_rx_ring_vaddr;
    device.tx_ring = (void *)hw_tx_ring_vaddr;

    net_queue_init(&rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    // Disable Interrupts, see Section 4.6.3.1
    disable_interrupts();

    // Master disable prior to link reset, see Section 4.2.1.7
    eth_regs->ctrl = IXGBE_CTRL_PCIE_MASTER_DISABLE;
    while (eth_regs->status & IXGBE_STATUS_PCIE_MASTER_STATUS);


    // Global Reset and General Configuration, see Section 4.6.3.2
    eth_regs->ctrl |= IXGBE_CTRL_RST;
    while ((eth_regs->ctrl & IXGBE_CTRL_RST_MASK) != 0);

    // Wait at least 10ms
    sddf_timer_set_timeout(timer_config.driver_id, 100 * NS_IN_MS);
}

void init_1(void)
{
    device.init_stage = 1;
    // section 4.6.3.1 - disable interrupts again after reset
    disable_interrupts();

    uint8_t mac[6];
    get_mac_addr(mac);
    sddf_dprintf("mac - %02x:%02x:%02x:%02x:%02x:%02x\n", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);

    // section 4.6.3 - wait for EEPROM auto read completion
    while((eth_regs->eec & IXGBE_EEC_ARD) != IXGBE_EEC_ARD);

    // section 4.6.3 - wait for dma initialization done
    while ((eth_regs->rdrxctl & IXGBE_RDRXCTL_DMAIDONE) != IXGBE_RDRXCTL_DMAIDONE);

    // section 4.6.4 - initialize link (auto negotiation)
    // link auto-configuration register should already be set correctly

    // negotiate link
    /* datasheet wants us to wait for the link here, but we can continue and wait afterwards */

    // section 4.6.5 - statistical counters
    // Initialise the Rx statistic registers.

    // section 4.6.5 - statistical counters
    // Initialise the Rx statistic registers.
    eth_regs->rqsmr[0] = 0;
    // reset-on-read registers, just read them once
    eth_regs->gprc;
    eth_regs->gptc;
    eth_regs->gorcl;
    eth_regs->gorch;
    eth_regs->gotcl;
    eth_regs->gotch;

    // section 4.6.7 - init rx
    {
        // disable rx while re-configuring it
        eth_regs->rxctrl &= (~IXGBE_RXCTRL_RXEN);

        // Section 8.2.2.8.23
        //   - Default MRQC: No DCB, No RSS: Queue 0 is used for all packets.

        eth_regs->rxpbsize[0] = IXGBE_RXPBSIZE_128KB;
        for (int i = 1; i < 8; i++) {
            eth_regs->rxpbsize[i] = 0;
        }

        eth_regs->hlreg0 |= IXGBE_HLREG0_RXCRCSTRP;
        eth_regs->rdrxctl |= IXGBE_RDRXCTL_CRCSTRIP;

        // accept broadcast packets, promiscuous
        eth_regs->fctrl |= IXGBE_FCTRL_BAM | IXGBE_FCTRL_MPE | IXGBE_FCTRL_UPE;

        // use only queue 0
        eth_regs->rx_dma[0].srrctl &= ~IXGBE_SRRCTL_DESCTYPE_MASK;
        eth_regs->rx_dma[0].srrctl |= IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF | IXGBE_SRRCTL_DROP_EN;
        eth_regs->rx_dma[0].rdbal = hw_rx_ring_paddr & 0xFFFFFFFFull;
        eth_regs->rx_dma[0].rdbah = hw_rx_ring_paddr >> 32;
        eth_regs->rx_dma[0].rdlen = NUM_RX_DESCS * sizeof(ixgbe_adv_rx_desc_t);
        eth_regs->rx_dma[0].rdh = 0;
        eth_regs->rx_dma[0].rdt = 0;

        eth_regs->ctrl_ext = IXGBE_CTRL_EXT_NS_DIS;
        eth_regs->rxctrl |= IXGBE_RXCTRL_RXEN;
        eth_regs->rx_dma[0].rxdctl = IXGBE_RXDCTL_ENABLE;
        while ((eth_regs->rx_dma[0].rxdctl & IXGBE_RXDCTL_ENABLE) == 0);
    }

    // section 4.6.8 - init tx
    {
        eth_regs->txpbsize[0] = IXGBE_TXPBSIZE_40KB;
        for (int i = 1; i < 8; i++) {
            eth_regs->txpbsize[i] = 0;
        }

        eth_regs->txpbthresh[0] = 0xA0;
        for (int i = 1; i < 8; i++) {
            eth_regs->txpbthresh[i] = 0;
        }

        eth_regs->tx_dma[0].tdbal = hw_tx_ring_paddr & 0xFFFFFFFFull;
        eth_regs->tx_dma[0].tdbah = hw_tx_ring_paddr >> 32;
        eth_regs->tx_dma[0].tdh = 0;
        eth_regs->tx_dma[0].tdt = 0;

        eth_regs->tx_dma[0].tdlen = NUM_TX_DESCS * sizeof(ixgbe_adv_tx_desc_t);

        // descriptor writeback magic values, important to get good performance and low PCIe overhead
        // see 7.2.3.4.1 and 7.2.3.5 for an explanation of these values and how to find good ones
        // we just use the defaults from DPDK here, but this is a potentially interesting point for optimizations
        // let mut txdctl = self.read_reg_idx(IxgbeArrayRegs::Txdctl, i);
        // there are no defines for this in ixgbe.rs for some reason
        // pthresh: 6:0, hthresh: 14:8, wthresh: 22:16

        // TODO: look at this
        eth_regs->tx_dma[0].txdctl &= ~(0x7F | (0x7F << 8) | (0x7F << 16)); // clear bits
        eth_regs->tx_dma[0].txdctl |= (36 | (8 << 8) | (4 << 16)); // from DPDK

        // final step: enable DMA
        eth_regs->dmatxctl = IXGBE_DMATXCTL_TE;
        eth_regs->tx_dma[0].txdctl = IXGBE_TXDCTL_ENABLE;
        while ((eth_regs->tx_dma[0].txdctl & IXGBE_TXDCTL_ENABLE) == 0);
    }

    // wait some time for the link to come up
    sddf_timer_set_timeout(timer_config.driver_id, 100 * NS_IN_MS);
}

void init_2(void)
{
    uint32_t speed = get_link_speed();
    if (speed == 0) {
        sddf_timer_set_timeout(timer_config.driver_id, 100 * NS_IN_MS);
        return;
    }

    device.init_stage = 2;

    // sleep for 10 seconds. Just stabilize the hardware
    // Well. this ugliness costed us two days of debugging.
    sddf_timer_set_timeout(timer_config.driver_id, 10 * NS_IN_S);
}

void init_3(void)
{
    device.init_stage = 3;

    rx_provide();
    tx_provide();

    enable_interrupts();

    sddf_dprintf("Finish NIC reset\n");
    device.init_stage = 4;
}

void notified(microkit_channel ch)
{
    if (ch == timer_config.driver_id) {
        if (device.init_stage == 0) {
            init_1();
        } else if (device.init_stage == 1) {
            init_2();
        } else if (device.init_stage == 2) {
            init_3();
        }
    } else if (device.init_stage != 4 && ch == 16) {
        sddf_deferred_irq_ack(ch);
    } else if (device.init_stage == 4) {
        if (ch == 16) {
            // read-to-clear
            uint32_t cause = eth_regs->eicr;
            if (cause & BIT(TX_IRQ_VECTOR)) {
                tx_return();
                tx_provide();
            }
            if (cause & BIT(RX_IRQ_VECTOR)) {
                rx_return();
                rx_provide();
            }

            /*
             * Delay calling into the kernel to ack the IRQ until the next loop
             * in the event handler loop.
             */
            sddf_deferred_irq_ack(ch);
        } else if (ch == config.virt_tx.id) {
            tx_provide();
        } else if (ch == config.virt_rx.id) {
            rx_provide();
        }
    }
}

