/*
 * Copyright 2026, Skykraft
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

/* HW ring capacity must be a power of 2 */
#define RX_COUNT 256
#define TX_COUNT 256
#define MAX_COUNT MAX(RX_COUNT, TX_COUNT)

/* HW ring descriptor, 64-bit (shared with device).
 * For RX, Word 0 (addr) also includes the wrap bit [1] and ownership bit [0] (Table 34-5)
 * For TX, Word 0 (addr) is only an address, wrap and ownership bits in Word 1 (stat) (Table 34-8)
 */
struct descriptor {
    uint32_t addr;      /* Word 0: Buffer address (RX: wrap + ownership as well) */
    uint32_t stat;      /* Word 1: Status/control */
    uint32_t addr_hi;   /* Word 2: Buffer address high (upper 32 bits) */
    uint32_t unused;
};

/* HW ring buffer data type */
typedef struct {
    uint32_t tail; /* index to insert at */
    uint32_t head; /* index to remove from */
    uint32_t capacity; /* capacity of the ring */
    volatile struct descriptor *descr; /* buffer descriptor array */
} hw_ring_t;

hw_ring_t rx; /* Rx NIC ring */
hw_ring_t tx; /* Tx NIC ring */

net_queue_handle_t rx_queue;
net_queue_handle_t tx_queue;

volatile zynqmp_gem_regs_t *eth;

static inline bool hw_ring_full(hw_ring_t *ring)
{
    return ring->tail - ring->head == ring->capacity;
}

static inline bool hw_ring_empty(hw_ring_t *ring)
{
    return ring->tail - ring->head == 0;
}

static void update_ring_slot_rx(hw_ring_t *ring, unsigned int idx, uintptr_t phys)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->addr_hi = (uint32_t)(phys >> 32);
    d->stat = 0;  /* HW fills on receive */
    
    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot. Recall d->addr includes ownership bit.
     */
    THREAD_MEMORY_RELEASE();
    
    d->addr = (uint32_t)(phys);
}

static void update_ring_slot_tx(hw_ring_t *ring, unsigned int idx, uintptr_t phys, uint16_t len, uint32_t stat)
{
    volatile struct descriptor *d = &(ring->descr[idx]);
    d->addr = (uint32_t)(phys);
    d->addr_hi = (uint32_t)(phys >> 32);

    /* Ensure all writes to the descriptor complete, before we set the flags
     * that makes hardware aware of this slot.
     */
    THREAD_MEMORY_RELEASE();

    d->stat = stat | (len & TXD_LEN_MASK);
}

static void rx_provide(void)
{
    bool reprocess = true;

    while (reprocess) {
        while (!hw_ring_full(&rx) && !net_queue_empty_free(&rx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&rx_queue, &buffer);
            assert(!err);

            uint32_t idx = rx.tail % rx.capacity;

            /* Buffer must be word-aligned; bits [1:0] are reserved by HW for wrap/ownership */
            assert((buffer.io_or_offset & ~RXD_ADDR_MASK) == 0);
            uintptr_t phys = buffer.io_or_offset;

            if (idx + 1 == rx.capacity) {
                phys |= RXD_WRAP;
            }

            update_ring_slot_rx(&rx, idx, phys);
            rx.tail++;
        }

        /* Only request a notification from virtualiser if HW ring not full */
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

    while (!hw_ring_empty(&rx)) {
        /* If buffer slot is still empty, we have processed all packets the device has filled */
        uint32_t idx = rx.head % rx.capacity;
        volatile struct descriptor *d = &(rx.descr[idx]);

        if (!(d->addr & RXD_OWN)) {
            break;
        }

        THREAD_MEMORY_ACQUIRE();

        /* See Table 34-5: RX Buffer Descriptor Entry (64-bit mode) */
        uint16_t len = d->stat & RXD_LEN_MASK;
        uintptr_t phys_addr = ((uintptr_t)d->addr_hi << 32) | (d->addr & RXD_ADDR_MASK);
        net_buff_desc_t buffer = { phys_addr, len };

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

static void tx_provide(void)
{
    bool reprocess = true;
    while (reprocess) {
        while (!hw_ring_full(&tx) && !net_queue_empty_active(&tx_queue)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_active(&tx_queue, &buffer);
            assert(!err);

            uint32_t idx = tx.tail % tx.capacity;
            uint32_t stat = TXD_LAST | TXD_MK_HW_OWNR; /* Set HW as owner */
            uintptr_t phys = buffer.io_or_offset;

            if (idx + 1 == tx.capacity) {
                stat |= TXD_WRAP;
            }

            update_ring_slot_tx(&tx, idx, phys, buffer.len, stat);
            tx.tail++;

            eth->nwctrl |= ZYNQ_GEM_NWCTRL_STARTTX_MASK;
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

        /* TXD_USED bit set by hardware when transmission complete */
        if (!(d->stat & TXD_USED)) {
            break;
        }

        THREAD_MEMORY_ACQUIRE();

        uintptr_t phys_addr = ((uintptr_t)d->addr_hi << 32) | (d->addr & TXD_ADDR_MASK);
        net_buff_desc_t buffer = { phys_addr, 0 };
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
    uint32_t isr = eth->isr & IRQ_MASK;
    uint32_t rxsr = eth->rxsr;
    uint32_t txsr = eth->txsr;
    eth->isr = isr;

    /* Clear any RX/TX status (write to clear) */
    if (rxsr) {
        eth->rxsr = rxsr;
    }
    if (txsr) {
        eth->txsr = txsr;
    }

    while (isr & IRQ_MASK) {
        if (isr & ZYNQ_INT_TXC) {
            tx_return();
            tx_provide();
        }
        if (isr & ZYNQ_INT_RXC) {
            rx_return();
            rx_provide();
        }
        isr = eth->isr & IRQ_MASK;
        eth->isr = isr;
    }
}

/** Disable unused priority queue 1 by pointing it at a permanent terminator descriptor
 * beyond the end of each active ring (i.e. at index RX_COUNT / TX_COUNT).
 * Disabled by having the SW-ownership bit set so hardware will never process it.
 * This region is never touched by rx_provide() / tx_provide(), so the terminator
 * state is stable for the lifetime of the driver.
 */
static void disable_pq1(void)
{
    volatile struct descriptor *rx_q1_terminator =
        (volatile struct descriptor *)(device_resources.regions[1].region.vaddr
                                       + rx.capacity * sizeof(struct descriptor));
    rx_q1_terminator->addr = RXD_OWN | RXD_WRAP; /* SW owns + wrap terminator */
    rx_q1_terminator->stat = 0;
    rx_q1_terminator->addr_hi = 0;

    volatile struct descriptor *tx_q1_terminator =
        (volatile struct descriptor *)(device_resources.regions[2].region.vaddr
                                       + tx.capacity * sizeof(struct descriptor));
    tx_q1_terminator->addr = 0;
    tx_q1_terminator->stat = TXD_USED | TXD_WRAP; /* SW owns + wrap terminator */
    tx_q1_terminator->addr_hi = 0;

    uintptr_t rx_q1_ptr = device_resources.regions[1].io_addr + rx.capacity * sizeof(struct descriptor);
    uintptr_t tx_q1_ptr = device_resources.regions[2].io_addr + tx.capacity * sizeof(struct descriptor);
    eth->receive_q1_ptr = (uint32_t)rx_q1_ptr;
    eth->transmit_q1_ptr = (uint32_t)tx_q1_ptr;
}

static void eth_setup(void)
{
    eth = (volatile zynqmp_gem_regs_t *)device_resources.regions[0].region.vaddr;

    uint32_t mac_l = eth->laddr[0][LADDR_LOW];
    uint32_t mac_h = eth->laddr[0][LADDR_HIGH];

    /* Set up HW rings */
    rx.descr = (volatile struct descriptor *)device_resources.regions[1].region.vaddr;
    tx.descr = (volatile struct descriptor *)device_resources.regions[2].region.vaddr;
    rx.capacity = RX_COUNT;
    tx.capacity = TX_COUNT;

    /* 1. Initialise controller - clear everything */
    eth->nwctrl = 0x0;
    eth->nwctrl |= ZYNQ_GEM_NWCTRL_CLEARSTAT;

    /* clear status regs */
    eth->rxsr = ZYNQ_GEM_RXSR_CLEAR;
    eth->txsr = ZYNQ_GEM_TXSR_CLEAR;

    /* disable interrupts */
    eth->idr = ZYNQ_GEM_IDR_CLEAR;

    /* clear rx/tx buffer queue */
    eth->rxqbase = 0x0;
    eth->txqbase = 0x0;

    /* clear hash regs */
    eth->hashl = 0x0;
    eth->hashh = 0x0;
    /* clear stat counters */
    for (int i = 0; i < STAT_SIZE; i++) {
        eth->stat[i] = 0x0;
    }
    /* 2 Network configuration */
    eth->nwcfg = 0x0;

    /* enable full duplex */
    eth->nwcfg |= ZYNQ_GEM_NWCFG_FDEN;

    /* enable FCS removal */
    eth->nwcfg |= ZYNQ_GEM_NWCFG_FSREM;

    /* 64 bit AMBA AXI data bus width */
    eth->nwcfg |= ZYNQ_GEM_DBUS_WIDTH;

    /* Gigabit speed */
    eth->nwcfg |= ZYNQ_GEM_NWCFG_SPEED1000;

    /* MDC clock divisor, for IEEE MDC < 2.5MHz */
    eth->nwcfg |= ZYNQ_GEM_NWCFG_IEEE_MDC;

    /* enable checksum offload on receive */
    eth->nwcfg |= ZYNQ_GEM_NWCFG_CHSUM_EN;

    /* copy all valid frames */
    eth->nwcfg |= ZYNQ_GEM_NWCFG_CPY_ALL_FRAMES;

    /* 3. Set MAC address */
    eth->laddr[0][LADDR_LOW] = mac_l;
    eth->laddr[0][LADDR_HIGH] = mac_h;

    /* 4. Configure DMA */
    eth->dmacr = 0x0;

    /* RX buffer size: 1536 bytes */
    eth->dmacr |= ZYNQ_GEM_DMACR_RXBUF;

    /* RX packet buffer: 32KB */
    eth->dmacr |= ZYNQ_GEM_DMACR_RXPBUF_32KB;

    /* TX packet buffer: 32KB */
    eth->dmacr |= ZYNQ_GEM_DMACR_TXPBUF_32KB;

    /* Enable TX checksum offload */
    eth->dmacr |= ZYNQ_GEM_DMACR_TXPBUF_TCP;

    /* AXI burst length: INCR16, 16 burst packets */
    eth->dmacr |= ZYNQ_GEM_DMACR_BLENGTH_16;

    /* 64-bit AXI bus width */
    eth->dmacr |= ZYNQ_GEM_DMA_BUS_WIDTH;

    /* 5. Initialise buffer descriptors */
    /* RX descriptors */
    for (uint32_t i = 0; i < rx.capacity; i++) {
        volatile struct descriptor *d = &(rx.descr[i]);
        d->addr = 0;
        d->stat = RXD_MK_HW_OWNR; /* HW owns initially */
        d->addr_hi = 0;
        if (i == rx.capacity - 1) {
            d->addr |= RXD_WRAP;
        }
    }

    /* TX descriptors */
    for (uint32_t i = 0; i < tx.capacity; i++) {
        volatile struct descriptor *d = &(tx.descr[i]);
        d->addr = 0;
        d->stat = TXD_USED; /* SW owns initially */
        d->addr_hi = 0;
        if (i == tx.capacity - 1) {
            d->stat |= TXD_WRAP;
        }
    }

    /* 6. Configure buffer descriptor queue addresses */
    /* Clear upper address registers
     * If you are actually using > 4GB memory addresses,
     * set this to your actual upper address bits
     */
    eth->upper_rxqbase = 0x0;
    eth->upper_txqbase = 0x0;

    /* Set rx/tx queue base address */
    eth->rxqbase = device_resources.regions[1].io_addr;
    eth->txqbase = device_resources.regions[2].io_addr;

    /* disable the unused priority queue 1 */
    disable_pq1();

    /* 7. Enable RX/TX interrupts */
    eth->ier = ZYNQ_INT_RXC | ZYNQ_INT_TXC;

    /* 8. Enable MDIO and transmitter (receiver enabled later after buffer init) */
    eth->nwctrl |= ZYNQ_GEM_NWCTRL_MDEN_MASK;
    eth->nwctrl |= ZYNQ_GEM_NWCTRL_TXEN_MASK;
}

void init(void)
{
    assert(net_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 3);

    /* All buffers should fit within our DMA region, plus one for queue1 terminator */
    assert((RX_COUNT + 1) * sizeof(struct descriptor) <= device_resources.regions[1].region.size);
    assert((TX_COUNT + 1) * sizeof(struct descriptor) <= device_resources.regions[2].region.size);

    eth_setup();

    net_queue_init(&rx_queue, config.virt_rx.free_queue.vaddr, config.virt_rx.active_queue.vaddr,
                   config.virt_rx.num_buffers);
    net_queue_init(&tx_queue, config.virt_tx.free_queue.vaddr, config.virt_tx.active_queue.vaddr,
                   config.virt_tx.num_buffers);

    rx_provide();
    tx_provide();

    /* Now that buffers are in the descriptor ring, enable the receiver */
    eth->nwctrl |= ZYNQ_GEM_NWCTRL_RXEN_MASK;
}

void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        /*
         * Delay calling into the kernel to ack the IRQ until the next loop
         * in the event handler loop.
         */
        sddf_deferred_irq_ack(ch);
    } else if (ch == config.virt_rx.id) {
        rx_provide();
    } else if (ch == config.virt_tx.id) {
        tx_provide();
    } else {
        sddf_dprintf("ETH|LOG: unexpected notification on channel: %u\n", ch);
    }
}