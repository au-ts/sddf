/*
 * Copyright 2021, Breakaway Consulting Pty. Ltd.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>
#include <sddf/util/printf.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/timer/client.h>
#include <ethernet_config.h>
#include <sddf/benchmark/bench.h>

#include "ixgbe.h"

#define assert(pred)                                \
    do {                                            \
        if (!pred) {                                \
            printf("assertion false: %s\n", #pred);	\
        }                                           \
    } while (0);

#define BIT(n) (1u << (n))
#define MASK(n) (~BIT(n))

#define IRQ_CH 0
#define TX_CH 1
#define RX_CH 2
#define TIMER_CH 3
#define COUNTER_CH 4

const uint64_t hw_rx_ring_paddr = 0x10000000;
const uint64_t hw_rx_ring_vaddr = 0x2200000;
const uint64_t hw_tx_ring_paddr = 0x10004000;
const uint64_t hw_tx_ring_vaddr = 0x2204000;
// const uint64_t hw_tx_ring_paddr = 0x10002000;
// const uint64_t hw_tx_ring_vaddr = 0x2202000;
const uintptr_t rx_free = 0x2400000;
const uintptr_t rx_used = 0x2600000;
const uintptr_t tx_free = 0x2800000;
const uintptr_t tx_used = 0x2a00000;

struct bench *bench = (void *)(uintptr_t)0x5010000;

const uint64_t ONE_MS_IN_NS = 1000000;

#define NUM_TX_DESCS 512llu
#define NUM_RX_DESCS 512llu
// #define NUM_TX_DESCS 1024llu
// #define NUM_RX_DESCS 1024llu
#define TX_CLEAN_BATCH 32llu

struct ixgbe_device {
    volatile ixgbe_adv_rx_desc_t *rx_ring;
    size_t rx_head, rx_tail;
    volatile ixgbe_adv_tx_desc_t *tx_ring;
    size_t tx_head, tx_tail;
    buff_desc_t rx_descr_mdata[NUM_RX_DESCS];
    buff_desc_t tx_descr_mdata[NUM_TX_DESCS];
    int init_stage;
} device;

ring_handle_t rx_ring;
ring_handle_t tx_ring;

static bool achieved_something;

void enable_interrupts(void);
void disable_interrupts(void);

static inline void set_reg(uintptr_t reg, uint32_t value) {
    __atomic_store_n(((volatile uint32_t *)reg), value, __ATOMIC_SEQ_CST);
}

static inline uint32_t get_reg(uintptr_t reg) {
	return __atomic_load_n((volatile uint32_t *)reg, __ATOMIC_SEQ_CST);
}

static inline void set_flags(uintptr_t reg, uint32_t flags) {
	set_reg(reg, get_reg(reg) | flags);
}

static inline void clear_flags(uintptr_t reg, uint32_t flags) {
	set_reg(reg, get_reg(reg) & ~flags);
}

static inline void set_reg16(uintptr_t reg, uint16_t value) {
    __atomic_store_n(((volatile uint16_t *)reg), value, __ATOMIC_SEQ_CST);
}

static inline uint16_t get_reg16(uintptr_t reg) {
	return __atomic_load_n((volatile uint16_t *)reg, __ATOMIC_SEQ_CST);
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

// static uint64_t I = 0;

void
tx_provide(void)
{
    // @jade: whyyy?
    // if (hw_rx_ring_empty()) {
    //     return;
    // }
    bool reprocess = true;
    while (reprocess) {
        bool provided = false;

        while (!(hw_tx_ring_full()) && !ring_empty(tx_ring.used_ring)) {
            achieved_something = true;
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_used(&tx_ring, &buffer);
            assert(!err);
            bench->eth_pcount_tx++;
            volatile ixgbe_adv_tx_desc_t *desc = &device.tx_ring[device.tx_tail];
            desc->read.buffer_addr = buffer.phys_or_offset;
            desc->read.cmd_type_len = IXGBE_ADVTXD_DCMD_EOP
                | IXGBE_ADVTXD_DCMD_RS
                | IXGBE_ADVTXD_DCMD_IFCS
                | IXGBE_ADVTXD_DCMD_DEXT
                | IXGBE_ADVTXD_DTYP_DATA
                | (uint32_t)buffer.len;
            desc->read.olinfo_status = ((uint32_t)buffer.len << IXGBE_ADVTXD_PAYLEN_SHIFT);

            THREAD_MEMORY_RELEASE();

            device.tx_descr_mdata[device.tx_tail] = buffer;

            device.tx_tail = (device.tx_tail + 1) % NUM_TX_DESCS;
            provided = true;
        }
        // @jade: should I move this to the outer block?
        if (provided) {
            THREAD_MEMORY_RELEASE();
            set_reg(TDT(0), device.tx_tail);
            bench->eth_tx_ntfn_count++;
        }

        request_signal(tx_ring.used_ring);
        reprocess = false;

        if (!hw_tx_ring_full() && !ring_empty(tx_ring.used_ring)) {
            cancel_signal(tx_ring.used_ring);
            reprocess = true;
        }
    }
}

void
tx_return(void)
{
    bool enqueued = false;
    while (!hw_tx_ring_empty() && !ring_full(tx_ring.free_ring)) {
        achieved_something = true;

        /* Ensure that this buffer has been sent by the device */
        ixgbe_adv_tx_desc_wb_t hw_desc = device.tx_ring[device.tx_head].wb;
        if ((hw_desc.status & IXGBE_ADVTXD_STAT_DD) == 0) break;

        THREAD_MEMORY_RELEASE();

        buff_desc_t descr_mdata = device.tx_descr_mdata[device.tx_head];
        int err __attribute__((unused)) = enqueue_free(&tx_ring, descr_mdata);
        assert(!err);
        enqueued = true;

        device.tx_head = (device.tx_head + 1) % NUM_TX_DESCS;
    }

    // if (enqueued) {
    //     bench->eth_tx_ntfn_count++;
    // }

    if (enqueued && require_signal(tx_ring.free_ring)) {
        cancel_signal(tx_ring.free_ring);
        microkit_notify(TX_CH);
    }
}

void
rx_provide(void)
{
    uint64_t rx_tail = device.rx_tail;

    bool reprocess = true;
    while (reprocess) {
        bool provided = false;

        while (!hw_rx_ring_full() && !ring_empty(rx_ring.free_ring)) {
            achieved_something = true;

            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_free(&rx_ring, &buffer);
            assert(!err);
            bench->eth_pcount_rx++;
            volatile ixgbe_adv_rx_desc_t *desc = &device.rx_ring[device.rx_tail];
            desc->read.pkt_addr = buffer.phys_or_offset;
            desc->read.hdr_addr = 0;

            THREAD_MEMORY_RELEASE();

            device.rx_descr_mdata[device.rx_tail] = buffer;

            device.rx_tail = (device.rx_tail + 1) % NUM_RX_DESCS;
            provided = true;
        }
        if (provided) {
            THREAD_MEMORY_RELEASE();
            set_reg(RDT(0), device.rx_tail);
        }

        /* Only request a notification from multiplexer if HW ring not full */
        if (!hw_rx_ring_full()) {
            request_signal(rx_ring.free_ring);
            // disable_interrupts();
        } else {
            cancel_signal(rx_ring.free_ring);
        }
        reprocess = false;

        if (!ring_empty(rx_ring.free_ring) && !hw_rx_ring_full()) {
            cancel_signal(rx_ring.free_ring);
            reprocess = true;
            // enable_interrupts();
        }
    }

    if (!(hw_rx_ring_empty())) {
        /* Ensure rx IRQs are enabled */
        // eth->rdar = RDAR_RDAR;
        // if (!(irq_mask & NETIRQ_RXF)) enable_irqs(IRQ_MASK);
    } else {
        // enable_irqs(NETIRQ_TXF | NETIRQ_EBERR);
    }

    uint64_t rx_tail_new = device.rx_tail;
    if (rx_tail != rx_tail_new) {
        // printf("rx_tail: old=%lu; new=%lu\n", rx_tail, rx_tail_new);
    }
}

static void rx_return(void)
{
    uint64_t rx_head = device.rx_head;

    bool packets_transferred = false;
    while (!hw_rx_ring_empty() && !ring_full(rx_ring.used_ring)) {
        achieved_something = true;

        /* If buffer slot is still empty, we have processed all packets the device has filled */
        ixgbe_adv_rx_desc_wb_t desc = device.rx_ring[device.rx_head].wb;
        if ((desc.upper.status_error & IXGBE_RXDADV_STAT_DD) == 0) break;
        if ((desc.upper.status_error & IXGBE_RXDADV_STAT_EOP) == 0) break;

        buff_desc_t buffer = device.rx_descr_mdata[device.rx_head];
        buffer.len = desc.upper.length;
        int err __attribute__((unused)) = enqueue_used(&rx_ring, buffer);
        assert(!err);

        // if (buffer.len != 60) {
        //     printf("received packet. len = %u\n", buffer.len);
        //     char *buf = (void *)buffer.phys_or_offset;
        //     printf("mac: %02x:%02x:%02x:%02x:%02x:%02x\n",
        //            buf[0x46], buf[0x47], buf[0x48], buf[0x49], buf[0x4a], buf[0x4b]);
        // }

        packets_transferred = true;
        device.rx_head = (device.rx_head + 1) % NUM_RX_DESCS;
    }

    if (packets_transferred && require_signal(rx_ring.used_ring)) {
        cancel_signal(rx_ring.used_ring);
        microkit_notify(RX_CH);
    }

    uint64_t rx_head_new = device.rx_head;
    if (rx_head != rx_head_new) {
        // printf("rx_head: old=%lu; new=%lu\n", rx_head, rx_head_new);
    }
}

void
clear_interrupts(void)
{
    set_reg(EIMC, IXGBE_IRQ_CLEAR_MASK);
    get_reg(EICR);
}

void
disable_interrupts(void)
{
    set_reg(EIMC, 0);
    clear_interrupts();
}

void
enable_interrupts(void)
{
    set_reg(IVAR(0), 1 | BIT(7) | (2 << 8) | BIT(15));

    set_reg(EIAC, 0);
    // set_reg(EITR(0), 0x028);
    clear_interrupts();
    // uint32_t mask = get_reg(EIMS);
    // mask |= ~BIT(31);
    // bit 15:0 for Receive/Transmit Queue Interrupts
    // set_reg(EIMS, BIT(0));
    set_reg(EIMS, 0xff);
    // set_reg(EIMS, 0xff | BIT(17));
    // set_reg(EIMS, ~BIT(31));
}

void
get_mac_addr(uint8_t mac[6])
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

uint64_t
get_link_speed(void)
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

void
dump_all_registers(void)
{
    printf("Interrupt regs:\n\tEICR: %08x EIMS: %08x\n\tGPIE %08x\n",
           get_reg(EICR), get_reg(EIMS), get_reg(GPIE));

    printf("Control regs:\n\tCTRL %08x CTRL_EXT %08x\n",
           get_reg(CTRL), get_reg(CTRL_EXT));

    printf("EEPROM regs:\n\tEEC_ARD %08x\n",
           get_reg(EEC));

    // printf("AUTOC %08x\n",
    //        get_reg(AUTOC));

    printf("Receive regs:\n\tRDRXCTRL %08x RXCTRL %08x\n\tHLREG0 %08x FCTRL %08x\n",
           get_reg(RDRXCTL),
           get_reg(RXCTRL),
           get_reg(HLREG0),
           get_reg(FCTRL));

    printf("Transmit regs:\n\tDTXMSSZRQ %08x RTTDCS %08x DMATXCTL: %08x\n",
           get_reg(DTXMXSZRQ),
           get_reg(RTTDCS),
           get_reg(DMATXCTL));

    printf("Stats regs:\n\tGPRC %08x GPTC %08x\n\tGORCL %08x GORCH %08x\n\tGOTCL %08x GOTCH %08x\n\tTXDGPC %08x TXDGBCH %08x TXDGBCL %08x QPTC(0) %08x\n",
           get_reg(GPRC),
           get_reg(GPTC),
           get_reg(GORCL),
           get_reg(GORCH),
           get_reg(GOTCL),
           get_reg(GOTCH),
           get_reg(TXDGPC),
           get_reg(TXDGBCH),
           get_reg(TXDGBCL),
           get_reg(QPTC(0)));
}

void
init(void)
{
    // printf("PCI command: %x\n", get_reg16(ECAM + 0x4));
    // set_flags16(ECAM + 0x4, BIT(10));
    // set_flags(ECAM + 0x52, 1);
    // set_reg(ECAM + 0x54, 0xFEEu << 20);
    // set_reg(ECAM + 0x58, 0);
    // set_reg(ECAM + 0x5c, 0x29);
    set_flags16(PCI_COMMAND_16, BIT(10));
    set_flags16(PCI_MSI_MESSAGE_CONTROL_16, BIT(0));
    clear_flags16(PCI_MSI_MESSAGE_CONTROL_16, BIT(4) | BIT(5) | BIT(6));
    set_reg(PCI_MSI_MESSAGE_ADDRESS_LOW, 0xFEEu << 20);
    set_reg(PCI_MSI_MESSAGE_ADDRESS_HIGH, 0);
    set_reg16(PCI_MSI_MESSAGE_DATA_16, 0x31);
    clear_flags16(PCI_MSI_MASK, BIT(0));

    // initialise the statistic registers. Must keep.
    set_reg(RQSMR(0), 0);

    printf("ethernet init stage 0 running\n");

    device.rx_ring = (void *)hw_rx_ring_vaddr;
    device.tx_ring = (void *)hw_tx_ring_vaddr;

    ring_init(&rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, RX_RING_SIZE_DRIV);
    ring_init(&tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, TX_RING_SIZE_DRIV);

    printf("disable irqs\n");
    disable_interrupts();

    printf("writing regs\n");
    set_reg(CTRL, IXGBE_CTRL_PCIE_MASTER_DISABLE);
    while (get_reg(STATUS) & IXGBE_STATUS_PCIE_MASTER_STATUS);

    // section 4.6.3.2
    set_reg(CTRL, IXGBE_CTRL_RST_MASK);
    while ((get_reg(CTRL) & IXGBE_CTRL_RST_MASK) != 0);

    printf("sleep\n");
    sddf_timer_set_timeout(TIMER_CH, 100 * ONE_MS_IN_NS);
}

void
init_1(void)
{
    device.init_stage = 1;
    printf("ethernet init stage 1 running\n");

    printf("resume after sleep\n");
    // section 4.6.3.1 - disable interrupts again after reset
    disable_interrupts();

    printf("no snoop disable bit\n");
    // check for no snoop disable bit
    // uint64_t ctrl_ext = *CTRL_EXT;
    // if ((ctrl_ext & IXGBE_CTRL_EXT_NS_DIS) == 0) {
    //     *CTRL_EXT = ctrl_ext | IXGBE_CTRL_EXT_NS_DIS;
    // }

    // *CTRL_EXT = IXGBE_CTRL_EXT_DRV_LOAD;

    uint8_t mac[6];
    get_mac_addr(mac);

    printf("initialising device\n");
    printf("   - MAC: %02X:%02X:%02X:%02X:%02X:%02X\n", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);

    // section 4.6.3 - wait for EEPROM auto read completion
    while ((get_reg(EEC) & IXGBE_EEC_ARD) != IXGBE_EEC_ARD);

    // section 4.6.3 - wait for dma initialization done
    while ((get_reg(RDRXCTL) & IXGBE_RDRXCTL_DMAIDONE) != IXGBE_RDRXCTL_DMAIDONE);

    // section 4.6.4 - initialize link (auto negotiation)
    // link auto-configuration register should already be set correctly, we're resetting it anyway
    // set_reg(AUTOC, (get_reg(AUTOC) & ~IXGBE_AUTOC_LMS_MASK) | IXGBE_AUTOC_LMS_10G_SERIAL);
    // set_reg(AUTOC, (get_reg(AUTOC) & ~IXGBE_AUTOC_10G_PMA_PMD_MASK) | IXGBE_AUTOC_10G_XAUI);

    // negotiate link
    // set_flags(AUTOC, IXGBE_AUTOC_AN_RESTART);
    // datasheet wants us to wait for the link here, but we can continue and wait afterwards

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
            set_reg(RDLEN(i), NUM_RX_DESCS * sizeof (ixgbe_adv_rx_desc_t));
            set_reg(RDH(0), 0);
            set_reg(RDT(0), 0);
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

        printf("tx ring %lu phys addr: 0x%lx\n", i, hw_tx_ring_paddr);
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
    printf("sleep until link up\n");
    sddf_timer_set_timeout(TIMER_CH, 100 * ONE_MS_IN_NS);
}

void
init_2(void)
{
    uint64_t speed = get_link_speed();
    if (speed == 0) {
        sddf_timer_set_timeout(TIMER_CH, 100 * ONE_MS_IN_NS);
        return;
    }

    device.init_stage = 2;
    printf("   - link speed is %lu Mbit/s\n", get_link_speed());
    printf("ethernet init stage 2 running\n");

    // dump_all_registers();

    // sleep for 10 seconds. Just stabilize the hardware
    // Well. this ugliness costed us two days of debugging.
    printf("sleep for 15 seconds\n");
    sddf_timer_set_timeout(TIMER_CH, 10 * 1000000000lu);
}

void
init_3(void)
{
    device.init_stage = 3;
    printf("ethernet init stage 3 running\n");

    rx_provide();
    tx_provide();

    enable_interrupts();

    device.init_stage = 4;

    // sddf_timer_set_timeout(TIMER_CH, 100 * NS_IN_MS);
}

void
handle_irq(void)
{
}

void
print_interrupt_regs(void)
{
    // printf("===== Interrupt regs ==================================================\n");
    // printf("\tPCI: COMMAND=0x%04x\n\t     STATUS=0x%04x\n\t     INT=0x%04x\n",
    //        get_reg16(PCI_VENDOR_ID_16),
    //        get_reg16(PCI_COMMAND_16),
    //        get_reg16(PCI_STATUS_16),
    //        get_reg16(PCI_INTERRUPT_PIN_LINE_16));
    // printf("\tMSI: MESSAGE_CONTROL=0x%04x\n\t     MESSAGE_ADDRESS_LOW=0x%08x\n\t     MESSAGE_ADDRESS_HIGH=0x%08x\n\t     MESSAGE_DATA=0x%04x\n\t     MASK=0x%08x\n\t     PENDING=0x%08x\n",
    //        get_reg16(PCI_MSI_MESSAGE_CONTROL_16),
    //        get_reg(PCI_MSI_MESSAGE_ADDRESS_LOW),
    //        get_reg(PCI_MSI_MESSAGE_ADDRESS_HIGH),
    //        get_reg16(PCI_MSI_MESSAGE_DATA_16),
    //        get_reg(PCI_MSI_MASK),
    //        get_reg(PCI_MSI_PENDING));
    // printf("\tDEV: EIMS=%0x%08x\n", get_reg(EIMS));
}

void
notified(microkit_channel ch)
{
    achieved_something = false;
    bench->eth_notified++;
    
    print_interrupt_regs();
    // printf("PCI interrupt pending? %d\n", get_reg16(ECAM + 0x6) & BIT(3) != 0);
    // printf("vendor id: %x\n", get_reg(ECAM));
    // clear_flags(ECAM + 0x60, 1);
    // printf("ECAM PBR: %x; MBR = %x\n", get_reg(ECAM + 0x64), get_reg(ECAM + 0x60));
    // printf("setting EIMS and EICS\n");
    // set_reg(EIMS, ~BIT(31));
    // set_reg(EICS, 1);
    // printf("ECAM PBR: %x\n", get_reg(ECAM + 0x64));
    // printf("PCI status reg: %x\n", get_reg16(ECAM + 0x6));

        // set EICS
    switch (ch) {
    case COUNTER_CH:
        uint64_t packets_count = get_reg(QPRC(0));
        bench->hw_pcount_rx = packets_count;

        uint64_t dropped_packets_count = get_reg(QPRDC(0));
        bench->hw_pcount_rx_dropped = dropped_packets_count;
        break;

    case TIMER_CH:
        achieved_something = true;
        if (device.init_stage == 0) {
            init_1();
        } else if (device.init_stage == 1) {
            init_2();
        } else if (device.init_stage == 2) {
            init_3();
        } // else if (device.init_stage == 4) {
        //     rx_return();
        //     tx_return();
        //     rx_provide();
        //     tx_provide();

        //     sddf_timer_set_timeout(TIMER_CH, 100 * NS_IN_MS);
        // }
        break;
    case IRQ_CH: {
        bench->eth_irq_count++;
        uint32_t cause = get_reg(EICR);
        clear_flags(EICR, cause);
        // if (cause && BIT(0)) {
            // rx_return();
            // rx_provide();
            // tx_return();
            // tx_provide();
        // }
        rx_return();
        rx_provide();
        if (achieved_something) {
            bench->eth_rx_irq_count++;
        }
        tx_return();
        tx_provide();
        // uint32_t cause = get_reg(EICR);
        // set_reg(EICR, 0);
        // handle_irq();
        /*
         * Delay calling into the kernel to ack the IRQ until the next loop
         * in the seL4CP event handler loop.
         */
        microkit_irq_ack_delayed(ch);
        break;
    }
    case RX_CH:
        if (device.init_stage == 4) {
            // enable_interrupts();
            rx_return();
            rx_provide();
        }
        break;
    case TX_CH:
        bench->eth_tx_ntfn_count++;

        if (device.init_stage == 4) {
            // enable_interrupts();
            tx_provide();
        }
        break;
    default:
        printf("ETH|LOG: received notification on unexpected channel: %X\n", ch);
        break;
    }
    if (!achieved_something) {
        bench->eth_idle_notified++;
    }

    // enable_interrupts();
}
