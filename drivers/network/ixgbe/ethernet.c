/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
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

#define MASK(n) (~BIT(n))

#define IRQ_CH 0
#define TX_CH 1
#define RX_CH 2
#define COUNTER_CH 4

#define RX_IRQ  1

// Minimum inter-interrupt interval specified in 2.048 us units
// at 1 GbE and 10 GbE link
// #define IRQ_INTERVAL 0
#define IRQ_INTERVAL 40

const uint64_t hw_rx_ring_paddr = 0x10000000;
const uint64_t hw_rx_ring_vaddr = 0x2400000;
const uint64_t hw_tx_ring_paddr = 0x10004000;
const uint64_t hw_tx_ring_vaddr = 0x2404000;

static bool achieved_something;

#define NUM_TX_DESCS 512llu
#define NUM_RX_DESCS 512llu
#define TX_CLEAN_BATCH 32llu

struct ixgbe_device {
    volatile ixgbe_adv_rx_desc_t *rx_ring;
    size_t rx_head, rx_tail;
    volatile ixgbe_adv_tx_desc_t *tx_ring;
    size_t tx_head, tx_tail;
    net_buff_desc_t rx_descr_mdata[NUM_RX_DESCS];
    net_buff_desc_t tx_descr_mdata[NUM_TX_DESCS];
    int init_stage;
} device;

/* HW ring descriptor (shared with device) */
struct descriptor {
    uint16_t len;
    uint16_t stat;
    uint32_t addr;
};

/* HW ring buffer data type */
typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of the ring */
    volatile struct descriptor *descr; /* buffer descriptor array */
} hw_ring_t;

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

#define MAX_PACKET_SIZE     1536

volatile struct enet_regs *eth;

static inline void set_reg(uintptr_t reg, uint32_t val) {
    asm volatile("movl %0,%1" : : "r" (val), "m" (*(volatile uint32_t *)reg));
}

static inline uint32_t get_reg(uintptr_t reg) {
    uint32_t ret;
    asm volatile("movl %1,%0" : "=r" (ret) : "m" (*(volatile uint32_t *)reg) : "memory");
    return ret;
}

static inline void set_flags(uintptr_t reg, uint32_t flags) {
    set_reg(reg, get_reg(reg) | flags);
}

static inline void clear_flags(uintptr_t reg, uint32_t flags) {
    set_reg(reg, get_reg(reg) & ~flags);
}

static inline void set_reg16(uintptr_t reg, uint16_t val) {
    asm volatile("movw %0,%1" : : "r" (val), "m" (*(volatile uint16_t *)reg));
}

static inline uint16_t get_reg16(uintptr_t reg) {
    uint16_t ret;
    asm volatile("movw %1,%0" : "=r" (ret) : "m" (*(volatile uint16_t *)reg) : "memory");
    return ret;
}

static inline void set_flags16(uintptr_t reg, uint16_t flags) {
    set_reg16(reg, get_reg16(reg) | flags);
}

static inline void clear_flags16(uintptr_t reg, uint16_t flags) {
    set_reg16(reg, get_reg16(reg) & ~flags);
}

static inline bool hw_tx_ring_empty(void)
{
    return device.tx_head == device.tx_tail;
}

static inline bool hw_tx_ring_full(void)
{
    return (device.tx_tail + 2) % NUM_TX_DESCS == device.tx_head;
}

static inline bool hw_rx_ring_empty(void)
{
    return device.rx_head == device.rx_tail;
}

static inline bool hw_rx_ring_full(void)
{
    return (device.rx_tail + 2) % NUM_RX_DESCS == device.rx_head;
}

void clear_interrupts(void)
{
    set_reg(EIMC, IXGBE_IRQ_CLEAR_MASK);
    get_reg(EICR); // Write Flush?
}

void disable_interrupts(void)
{
    set_reg(EIMC, 0);
    clear_interrupts();
}

void enable_interrupts(void)
{
    // set_reg(IVAR(0), RX_IRQ | BIT(7) | (2 << 8) | BIT(15));
    // @jade: we don't enable TX IRQ, just do TX complete on RX event
    set_reg(IVAR(0), RX_IRQ | BIT(7));

    set_reg(EIAC, 0);
    // @jade: enable auto clear (actually, what is it?)
    // set_reg(EIAC, BIT(0));
    set_reg(EITR(0), IXGBE_EITR_ITR_INTERVAL * IRQ_INTERVAL);
    // set_reg(EITR(0), 0x028);
    clear_interrupts();
    // uint32_t mask = get_reg(EIMS);
    // mask |= ~BIT(31);

    // bit 15:0 for Receive/Transmit Queue Interrupts. We only enable those IRQs
    // because the driver doesn't know how to handle IRQs caused by other reasons.
    // set_reg(EIMS, ~BIT(31));
    // set_reg(EIMS, BIT(1));
    set_reg(EIMS, 0xff);
}

void get_mac_addr(uint8_t mac[6])
{
    uint64_t low = get_reg(RAL(0));
    uint64_t high = get_reg(RAH(0));

    mac[0] = low & 0xff;
    mac[1] = low >> 8 & 0xff;
    mac[2] = low >> 16 & 0xff;
    mac[3] = low >> 24;
    mac[4] = high & 0xff;
    mac[5] = high >> 8 & 0xff;
}

uint64_t get_link_speed(void)
{
    uint64_t speed = get_reg(LINKS);
    if ((speed & IXGBE_LINKS_UP) == 0) {
        return 0;
    }
    switch (speed & IXGBE_LINKS_SPEED_82599) {
    case IXGBE_LINKS_SPEED_100_82599: return 100;
    case IXGBE_LINKS_SPEED_1G_82599: return 1000;
    case IXGBE_LINKS_SPEED_10G_82599: return 10000;
    default:
        return 0;
    }
}

void tx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        bool provided = false;

        while (!(hw_tx_ring_full()) && !net_queue_empty_active(&tx_queue)) {

            // we have a packet to process, that's an achievement!
            achieved_something = true;

            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            /* bench->eth_pcount_tx++; */

            volatile ixgbe_adv_tx_desc_t *desc = &device.tx_ring[device.tx_tail];
            desc->read.buffer_addr = buffer.io_or_offset;
            desc->read.cmd_type_len = IXGBE_ADVTXD_DCMD_EOP
                | IXGBE_ADVTXD_DCMD_RS
                | IXGBE_ADVTXD_DCMD_IFCS
                | IXGBE_ADVTXD_DCMD_DEXT
                | IXGBE_ADVTXD_DTYP_DATA
                | (uint32_t)buffer.len;
            desc->read.olinfo_status = ((uint32_t)buffer.len << IXGBE_ADVTXD_PAYLEN_SHIFT);

            /* THREAD_MEMORY_RELEASE(); */

            device.tx_descr_mdata[device.tx_tail] = buffer;

            device.tx_tail = (device.tx_tail + 1) % NUM_TX_DESCS;
            provided = true;
        }
        // @jade: should I move this to the outer block?
        if (provided) {
            /* THREAD_MEMORY_RELEASE(); */
            set_reg(TDT(0), device.tx_tail);
            get_reg(TDT(0));
        }

        net_request_signal_active(&tx_queue);
        reprocess = false;

        // @jade: we optimised this on RX, should we do it on TX as well?
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
        // we are putting a buffer back into TX free queue, an achievement!
        achieved_something = true;

        /* Ensure that this buffer has been sent by the device */
        ixgbe_adv_tx_desc_wb_t hw_desc = device.tx_ring[device.tx_head].wb;
        if ((hw_desc.status & IXGBE_ADVTXD_STAT_DD) == 0) break;

        THREAD_MEMORY_RELEASE();

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

            // desc->wb.upper.status_error &= ~IXGBE_RXDADV_STAT_DD;
            // desc->wb.upper.status_error &= ~IXGBE_RXDADV_STAT_EOP;
            THREAD_MEMORY_RELEASE();

            device.rx_descr_mdata[device.rx_tail] = buffer;

            device.rx_tail = (device.rx_tail + 1) % NUM_RX_DESCS;
            provided = true;
        }

        if (provided) {
            THREAD_MEMORY_RELEASE();
            set_reg(RDT(0), device.rx_tail);
        }

        /* Only request a notification from multiplexer if HW ring is empty */
        if (hw_rx_ring_empty()) {
            /* bench->eth_request_signal_rx++; */
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
        // @jade: why do we get into this loop all the time even when there is no packets in there?
        // achieved_something = true;

        /* If buffer slot is still empty, we have processed all packets the device has filled */
        ixgbe_adv_rx_desc_wb_t desc = device.rx_ring[device.rx_head].wb;
        if ((desc.upper.status_error & IXGBE_RXDADV_STAT_DD) == 0) break;
        if ((desc.upper.status_error & IXGBE_RXDADV_STAT_EOP) == 0) break;

        net_buff_desc_t buffer = device.rx_descr_mdata[device.rx_head];
        buffer.len = desc.upper.length;
        int err = net_enqueue_active(&rx_queue, buffer);
        assert(!err);

        // we are putting a buffer back into RX active queue, an achievement!
        achieved_something = true;

        /* bench->eth_pcount_rx++; */

        packets_transferred = true;
        device.rx_head = (device.rx_head + 1) % NUM_RX_DESCS;
    }

    if (packets_transferred && net_require_signal_active(&rx_queue)) {
        net_cancel_signal_active(&rx_queue);
        /* bench->eth_rx_notify++; */
        microkit_notify(config.virt_rx.id);
    }
}

void init(void)
{
    // Enable MSI, refer to https://www.intel.com/content/www/us/en/docs/programmable/683488/16-0/msi-registers.html
    set_flags16(PCI_COMMAND_16, BIT(10));
    set_flags16(PCI_MSI_MESSAGE_CONTROL_16, BIT(0));
    clear_flags16(PCI_MSI_MESSAGE_CONTROL_16, BIT(4) | BIT(5) | BIT(6));
    set_reg(PCI_MSI_MESSAGE_ADDRESS_LOW, 0xFEEu << 20);
    set_reg(PCI_MSI_MESSAGE_ADDRESS_HIGH, 0);
    set_reg16(PCI_MSI_MESSAGE_DATA_16, 0x31);
    clear_flags16(PCI_MSI_MASK, BIT(0));

    /* sddf_dprintf("\n"); */
    /* sddf_dprintf("NIC vendor_id: 0x%x\n", get_reg16(0x3100000)); */
    /* sddf_dprintf("NIC device_id: 0x%x\n", get_reg16(0x3100002)); */
    /* sddf_dprintf("NIC command: 0x%x\n", get_reg16(0x3100004)); */
    /* sddf_dprintf("NIC status: 0x%x\n", get_reg16(0x3100006)); */
    /* sddf_dprintf("NIC offset 0x10: 0x%x\n", get_reg(0x3100010)); */
    /* sddf_dprintf("NIC offset 0x20: 0x%x\n", get_reg(0x3100020)); */
    /* sddf_dprintf("NIC offset 0x30: 0x%x\n", get_reg(0x3100030)); */
    /* sddf_dprintf("FACTPS reg: 0x%x\n", get_reg(FACTPS)); */
    /* sddf_dprintf("CTRL reg: 0x%x\n", get_reg(CTRL)); */

    // initialise the statistic registers. Must keep.
    set_reg(RQSMR(0), 0);

    /* sddf_dprintf("ethernet init stage 0 running\n"); */

    device.rx_ring = (void *)hw_rx_ring_vaddr;
    device.tx_ring = (void *)hw_tx_ring_vaddr;

    /* net_queue_init(&rx_queue, rx_free, rx_active, NET_RX_QUEUE_CAPACITY_DRIV); */
    /* net_queue_init(&tx_queue, tx_free, tx_active, NET_TX_QUEUE_CAPACITY_DRIV); */
    net_queue_init(&rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    // Disable Interrupts, see Section 4.6.3.1
    /* sddf_dprintf("disable irqs\n"); */
    disable_interrupts();

    /* sddf_dprintf("writing regs\n"); */
    set_reg(CTRL, IXGBE_CTRL_PCIE_MASTER_DISABLE);
    while (get_reg(STATUS) & IXGBE_STATUS_PCIE_MASTER_STATUS);
    /* sddf_dprintf("CTRL: 0x%x\n", get_reg(CTRL)); */

    /* Global Reset and General Configuration, see Section 4.6.3.2 */
    set_reg(CTRL, get_reg(CTRL) | IXGBE_CTRL_RST);
    /* sddf_dprintf("CTRL: 0x%x, EEC: 0x%x\n", get_reg(CTRL), get_reg(EEC)); */
    while ((get_reg(CTRL) & IXGBE_CTRL_RST_MASK) != 0);

    /* sddf_dprintf("sleep\n"); */
    sddf_timer_set_timeout(timer_config.driver_id, 100 * NS_IN_MS);
}

void init_1(void)
{
    device.init_stage = 1;
    sddf_dprintf("ethernet init stage 1 running\n");

    sddf_dprintf("resume after sleep\n");
    // section 4.6.3.1 - disable interrupts again after reset
    disable_interrupts();

    sddf_dprintf("no snoop disable bit\n");
    // check for no snoop disable bit
    // uint64_t ctrl_ext = *CTRL_EXT;
    // if ((ctrl_ext & IXGBE_CTRL_EXT_NS_DIS) == 0) {
    //     *CTRL_EXT = ctrl_ext | IXGBE_CTRL_EXT_NS_DIS;
    // }

    // *CTRL_EXT = IXGBE_CTRL_EXT_DRV_LOAD;

    uint8_t mac[6];
    get_mac_addr(mac);

    sddf_dprintf("initialising device\n");
    sddf_dprintf("   - MAC: %02X:%02X:%02X:%02X:%02X:%02X\n", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);

    // section 4.6.3 - wait for EEPROM auto read completion
    while ((get_reg(EEC) & IXGBE_EEC_ARD) != IXGBE_EEC_ARD);
    sddf_dprintf("EEC: 0x%x\n", get_reg(EEC));

    // section 4.6.3 - wait for dma initialization done
    while ((get_reg(RDRXCTL) & IXGBE_RDRXCTL_DMAIDONE) != IXGBE_RDRXCTL_DMAIDONE);

    // section 4.6.4 - initialize link (auto negotiation)
    // link auto-configuration register should already be set correctly, we're resetting it anyway
    /* set_reg(AUTOC, (get_reg(AUTOC) & ~IXGBE_AUTOC_LMS_MASK) | IXGBE_AUTOC_LMS_10G_SERIAL); */
    /* set_reg(AUTOC, (get_reg(AUTOC) & ~IXGBE_AUTOC_10G_PMA_PMD_MASK) | IXGBE_AUTOC_10G_XAUI); */

    // negotiate link
    /* set_flags(AUTOC, IXGBE_AUTOC_AN_RESTART); */
    /* datasheet wants us to wait for the link here, but we can continue and wait afterwards */

    // section 4.6.5 - statistical counters
    // reset-on-read registers, just read them once
    get_reg(GPRC);
    get_reg(GPTC);
    get_reg(GORCL);
    get_reg(GORCH);
    get_reg(GOTCL);
    get_reg(GOTCH);

    // section 4.6.7 - init rx
    {
        // disable rx while re-configuring it
        clear_flags(RXCTRL, IXGBE_RXCTRL_RXEN);

        set_reg(RXPBSIZE(0), IXGBE_RXPBSIZE_128KB);
        for (int i = 1; i < 8; i++) {
            set_reg(RXPBSIZE(i), 0);
        }

        set_flags(HLREG0, IXGBE_HLREG0_RXCRCSTRP);
        set_flags(RDRXCTL, IXGBE_RDRXCTL_CRCSTRIP);

        // accept broadcast packets, promiscuous
        set_flags(FCTRL, IXGBE_FCTRL_BAM | IXGBE_FCTRL_MPE | IXGBE_FCTRL_UPE);

        // only use queue 0
        for (int i = 0; i < 1; i++) {
            set_reg(SRRCTL(i), (get_reg(SRRCTL(i)) & ~IXGBE_SRRCTL_DESCTYPE_MASK) | IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF);
            set_reg(SRRCTL(i), get_reg(SRRCTL(i)) | IXGBE_SRRCTL_DROP_EN);

            set_reg(RDBAL(i), hw_rx_ring_paddr & 0xFFFFFFFFull);
            set_reg(RDBAH(i), hw_rx_ring_paddr >> 32);
            sddf_dprintf("RDBAL: 0x%x\n", get_reg(RDBAL(i)));
            set_reg(RDLEN(i), NUM_RX_DESCS * sizeof (ixgbe_adv_rx_desc_t));
            sddf_dprintf("RDLEN: 0x%x\n", get_reg(RDLEN(i)));
            set_reg(RDH(0), 0);
            set_reg(RDT(0), 0);
            sddf_dprintf("RDH: 0x%x, RDT: 0x%x\n", get_reg(RDH(0)), get_reg(RDT(0)));
        }

        set_reg(CTRL_EXT, IXGBE_CTRL_EXT_NS_DIS);

        // for (int i = 0; i < 1; i++) {
        //     clear_flags(DCA_RXCTRL(i), 1 << 12);
        // }

        set_flags(RXCTRL, IXGBE_RXCTRL_RXEN);
        set_reg(RXDCTL(0), IXGBE_RXDCTL_ENABLE);
        while ((get_reg(RXDCTL(0)) & IXGBE_RXDCTL_ENABLE) == 0);
    }

    // section 4.6.8 - init tx
    {
        // crc offload and small packet padding
        // *HLREG0 |= IXGBE_HLREG0_TXCRCEN | IXGBE_HLREG0_TXPADEN;

        // required when not using DCB/VTd
        // *DTXMXSZRQ = 0xFFFF;
        // *RTTDCS &= ~IXGBE_RTTDCS_ARBDIS;

        // section 7.1.9 - setup descriptor ring

        // configure a single transmit queue/ring
        const uint64_t i = 0;

        // section 4.6.11.3.4 - set default buffer size allocations
        set_reg(TXPBSIZE(0), IXGBE_TXPBSIZE_40KB);
        for (uint64_t j = 1; j < 8; j++) {
            set_reg(TXPBSIZE(j), 0);
        }

        set_reg(TXPBTHRESH(0), 0xA0);
        for (uint64_t j = 1; j < 8; j++) {
            set_reg(TXPBTHRESH(j), 0);
        }

        set_reg(TDBAL(i), hw_tx_ring_paddr & 0xFFFFFFFFull);
        set_reg(TDBAH(i), hw_tx_ring_paddr >> 32);
        set_reg(TDH(0), 0);
        set_reg(TDT(0), 0);

        sddf_dprintf("tx ring %lu phys addr: 0x%lx\n", i, hw_tx_ring_paddr);
        set_reg(TDLEN(i), NUM_TX_DESCS * sizeof (ixgbe_adv_tx_desc_t));

        // descriptor writeback magic values, important to get good performance and low PCIe overhead
        // see 7.2.3.4.1 and 7.2.3.5 for an explanation of these values and how to find good ones
        // we just use the defaults from DPDK here, but this is a potentially interesting point for optimizations
        //let mut txdctl = self.read_reg_idx(IxgbeArrayRegs::Txdctl, i);
        // there are no defines for this in ixgbe.rs for some reason
        // pthresh: 6:0, hthresh: 14:8, wthresh: 22:16
        //txdctl &= !(0x3F | (0x3F << 8) | (0x3F << 16));
        //txdctl |= 36 | (8 << 8) | (4 << 16);

        uint32_t txdctl = get_reg(TXDCTL(i));
        // pthresh: 6:0, hthresh: 14:8, wthresh: 22:16
        txdctl &= ~(0x7F | (0x7F << 8) | (0x7F << 16)); // clear bits
        txdctl |= (36 | (8 << 8) | (4 << 16)); // from DPDK
        set_reg(TXDCTL(i), txdctl);

        // final step: enable DMA

        set_reg(DMATXCTL, IXGBE_DMATXCTL_TE);
        set_reg(TXDCTL(0), IXGBE_TXDCTL_ENABLE);
        while ((get_reg(TXDCTL(0)) & IXGBE_TXDCTL_ENABLE) == 0);
    }


    // wait some time for the link to come up
    sddf_dprintf("sleep until link up\n");
    sddf_timer_set_timeout(timer_config.driver_id, 100 * NS_IN_MS);
}

void init_2(void)
{
    uint64_t speed = get_link_speed();
    if (speed == 0) {
        sddf_timer_set_timeout(timer_config.driver_id, 100 * NS_IN_MS);
        return;
    }

    device.init_stage = 2;
    sddf_dprintf("   - link speed is %lu Mbit/s\n", get_link_speed());
    sddf_dprintf("ethernet init stage 2 running\n");

    // dump_all_registers();

    // sleep for 10 seconds. Just stabilize the hardware
    // Well. this ugliness costed us two days of debugging.
    sddf_dprintf("sleep for 15 seconds\n");
    sddf_timer_set_timeout(timer_config.driver_id, 10 * NS_IN_S);
}

void init_3(void)
{
    device.init_stage = 3;
    sddf_dprintf("ethernet init stage 3 running\n");

    rx_provide();
    tx_provide();

    sddf_dprintf("enable interrupts\n");
    enable_interrupts();

    device.init_stage = 4;

    sddf_dprintf("ethernet init finished\n");
    /* sddf_timer_set_timeout(timer_config.driver_id, 1 * NS_IN_S); */
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
    } else if (ch == device_resources.irqs[0].id){
        /* bench->eth_irq_count++; */
        // write/read-to-clear, no need for auto clear
        uint32_t cause = get_reg(EICR);
        clear_flags(EICR, cause);
        tx_return();
        tx_provide();
        achieved_something = false;
        rx_return();
        rx_provide();
        /* if (achieved_something) { */
        /*     bench->eth_rx_irq_count++; */
        /* } */
        /*
         * Delay calling into the kernel to ack the IRQ until the next loop
         * in the seL4CP event handler loop.
         */
        microkit_deferred_irq_ack(ch);
    } else if (ch == config.virt_tx.id) {
        if (device.init_stage == 4) {
            tx_provide();
        }
    } else if (ch == config.virt_rx.id) {
        if (device.init_stage == 4) {
            rx_provide();
        }
    }
}
