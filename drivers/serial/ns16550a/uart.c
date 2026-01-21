/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/serial/config.h>
#include <sddf/serial/queue.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>
#include "uart.h"

__attribute__((__section__(".serial_driver_config"))) serial_driver_config_t config;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

/* UART device registers */
volatile uintptr_t uart_base;

/* TODO: Use the value from the device tree*/
#if defined(CONFIG_PLAT_STAR64) || defined(CONFIG_PLAT_CHESHIRE) || defined(CONFIG_PLAT_BCM2711)                       \
    || defined(CONFIG_PLAT_HIFIVE_P550)
#define REG_IO_WIDTH 4
#define REG_SHIFT 2
#define REG_PTR(off)     ((volatile uint32_t *)((uart_base) + (off << REG_SHIFT)))
#elif defined(CONFIG_PLAT_QEMU_RISCV_VIRT)
#define REG_IO_WIDTH 1
#define REG_SHIFT 0
#define REG_PTR(off)     ((volatile uint8_t *)((uart_base) + (off << REG_SHIFT)))
#else
#error "unknown platform reg-io-width"
#endif

static inline bool tx_fifo_not_full(void)
{
#if UART_DW_APB_REGISTERS && !defined(CONFIG_PLAT_HIFIVE_P550)
    /**
     * On DesignWare APB-derived 16550a-like IPs, they provide a TFNF bit in
     * the UART Status Register (USR).
     */
    return !!(*REG_PTR(UART_USR) & UART_USR_TFNF);
#else
    /**
     * On a standard NS16550a UART IP, we don't have a "transmit FIFO (not) full"
     * indicator bit. Instead we have a FIFO empty / holding register empty bit.
     * This means that despite *notionally* having a TX FIFO, it is never filled
     * more than 1 bit at a time. This makes the TX rather slow. If we only use
     * this on our Star64, we see interleaved serial output in debug mode [1].
     *
     * Ref [2] also describes this similar issue, and demonstrates the "intended"
     * use is to write a FIFO-size (i.e. 16 characters) at once to the UART THR.
     * This is also what Zephyr [3] and Linux [4] do.
     *
     * However, as we run on top of seL4, we may be preempted at any time.
     * Specifically, another process may use a debug print through OpenSBI's
     * driver [5] which will write to the UART THR. Because a TX overrun on the
     * NS16550a will corrupt what had previously been written (as opposed to
     * not doing anything), we can't detect whether or not we would corrupt
     * the serial output.
     *
     * It would be possible, if OpenSBI's driver handled "polling uart in an IRQ
     * context" like Linux does [6], where it wants for the THR to empty both
     * before *and* after emitting a character. However, this is not the case.
     *
     * Hence, on standard ns16550a we are likely to see interleaved serial output
     * because of how slow waiting for an interrupt for *every* output character
     * is.
     *
     * [1]: https://github.com/au-ts/sddf/issues/411#issuecomment-2864845777
     * [2]: https://www.ele.uva.es/~jesus/UltimatePutchar.pdf
     * [3]: https://github.com/zephyrproject-rtos/zephyr/blob/zephyr-v3.5.0/drivers/serial/uart_ns16550.c#L773-L798
     * [4]: https://github.com/torvalds/linux/blob/v6.14/drivers/tty/serial/8250/8250_port.c#L1794-L1855
     * [5]: https://github.com/riscv-software-src/opensbi/blob/v1.6/lib/utils/serial/uart8250.c#L74-L80
     * [6]: https://github.com/torvalds/linux/commit/f2d937f3bf00665ccf048b3b6616ef95859b0945
     */
    return !!(*REG_PTR(UART_LSR) & UART_LSR_THRE);
#endif
}

static inline bool rx_has_data(void)
{
    return !!(*REG_PTR(UART_LSR) & UART_LSR_DR);
}

static void set_baud(unsigned long baud)
{
    /*  Divisor Latch Access Bit (DLAB) of the LCR must be set.
    *   These registers share their address with the FIFO's.
    */
#if UART_DW_APB_REGISTERS
    /*
     * From the specification for DLH:
     * "This register may only be accessed when the DLAB bit (LCR[7]) is set
     * and the UART is not busy (USR[0] is zero)"
     */
    while (*REG_PTR(UART_USR) & UART_USR_BUSY);
#endif

    uint32_t lcr_val = *REG_PTR(UART_LCR);

    *REG_PTR(UART_LCR) |= UART_LCR_DLAB;

    /* baud rate = (serial_clock_freq) / (16 * divisor) */
    uint16_t divisor = DIV_ROUND_CLOSEST(UART_CLK, 16 * baud);

    *REG_PTR(UART_DLH) = (divisor >> 8) & 0xff;
    *REG_PTR(UART_DLL) = divisor & 0xff;

    /* Restore the LCR */
    *REG_PTR(UART_LCR) = lcr_val;
}

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (tx_fifo_not_full() && !serial_dequeue(&tx_queue_handle, &c)) {
        *REG_PTR(UART_THR) = c;
        transferred = true;
    }

    /* If we still have data to be sent after filling the FIFO, enable TX empty IRQ */
    if (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        *REG_PTR(UART_IER) |= UART_IER_ETBEI;
    } else {
        *REG_PTR(UART_IER) &= ~UART_IER_ETBEI;
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        sddf_notify(config.tx.id);
    }
}

static void rx_return(void)
{
    bool reprocess = true;
    bool enqueued = false;
    while (reprocess) {
        while (rx_has_data() && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            char c = *REG_PTR(UART_RBR);
            int err = serial_enqueue(&rx_queue_handle, c);
            assert(!err);
            enqueued = true;
        }

        /* If we have more RX device data available, but no space in the queue with the virtualiser,
         * we disable RX IRQs until space becomes available. */
        if (rx_has_data() && serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            *REG_PTR(UART_IER) &= ~UART_IER_ERBFI;
            serial_request_consumer_signal(&rx_queue_handle);
        }

        reprocess = false;

        /* While RX data is still available, we enable the RX IRQ and continue processing */
        if (rx_has_data() && !serial_queue_full(&rx_queue_handle, rx_queue_handle.queue->tail)) {
            serial_cancel_consumer_signal(&rx_queue_handle);
            *REG_PTR(UART_IER) |= UART_IER_ERBFI;
            reprocess = true;
        }
    }

    if (enqueued) {
        sddf_notify(config.rx.id);
    }
}

static void handle_irq(void)
{
    /* Reading this register auto-clears the error bits.
       So we have to do this before rx_return() / tx_provide() which needs to
       read LSR for THRE/DR. */
    uint32_t line_status = *REG_PTR(UART_LSR);
    if (line_status & (UART_LSR_PE | UART_LSR_FE | UART_LSR_RFE)) {
        LOG_DRIVER_ERR("LSR had error bits set %x\n", line_status);
    }

    /* IRQ ID is a priority-based *single* indication, not a bitvector */
    uint8_t irq_id = *REG_PTR(UART_IIR) & UART_IIR_IID_MASK;
    if (config.rx_enabled && irq_id == UART_IIR_IID_RDI) {
        rx_return();
    } else if (irq_id == UART_IIR_IID_THRI) {
        tx_provide();
    }
}

void init(void)
{
    assert(serial_config_check_magic(&config));
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    uart_base = (uintptr_t)device_resources.regions[0].region.vaddr;

    /* Ensure that the FIFO's are empty */
    while (!(*REG_PTR(UART_LSR) & (UART_LSR_THRE | UART_LSR_TEMT)));

    /* Disable all interrupts for now */
    *REG_PTR(UART_IER) = 0;

    /* Clear any error indication bits */
    (void)*REG_PTR(UART_LSR);
    /* Reset interrupt indications. */
    (void)*REG_PTR(UART_IIR);

    /* Setup the Modem Control Register */
    *REG_PTR(UART_MCR) = (UART_MCR_DTR | UART_MCR_RTS);

    /* Reset and enable the FIFO's*/
    *REG_PTR(UART_FCR) = (UART_FCR_XFIFOR | UART_FCR_RFIFOR | UART_FCR_FIFOE);

    /* Set LCR format; 8 bit data length (bits 0-1), 1 stop bit (bit 2),
       no parity, no break control. */
    *REG_PTR(UART_LCR) = 0b00000011;

    /* Set the baud rate */
    set_baud(config.default_baud);

    if (config.rx_enabled) {
        /* Enable (only) the receive data available IRQ
           -> TX enabled as needed by tx_provide(). */
        *REG_PTR(UART_IER) = UART_IER_ERBFI;

        serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    }

    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

#if UART_DW_APB_REGISTERS
    /* Clear the USR busy bit
     * This must be done after enabling IRQs
     * https://github.com/torvalds/linux/blob/v6.14/drivers/tty/serial/8250/8250_dw.c#L304-L306
     */
    (void)*REG_PTR(UART_USR);
#endif
}

void notified(sddf_channel ch)
{
    if (ch == device_resources.irqs[0].id) {
        handle_irq();
        sddf_deferred_irq_ack(ch);
    } else if (ch == config.tx.id) {
        tx_provide();
    } else if (ch == config.rx.id) {
        rx_return();
    } else {
        LOG_DRIVER_ERR("received notification on unexpected channel\n");
    }
}
