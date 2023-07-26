/*
* Sample serial driver for odroid c4 (amlogic meson gx uart) based on the sDDF
*/

#include <stdbool.h>
#include <stdint.h>
#include <sel4cp.h>
#include <sel4/sel4.h>
#include "uart.h"
#include "shared_ringbuffer.h"

#define BIT(nr) (1UL << (nr))

// Defines to manage interrupts and notifications
#define IRQ_CH 1
#define TX_CH  8
#define RX_CH  10

/* Memory regions. These all have to be here to keep compiler happy */
// Ring handle components
uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;
uintptr_t shared_dma_vaddr;
uintptr_t shared_dma_paddr;
uintptr_t shared_dma_rx_drv;
// Base of the uart registers
uintptr_t uart_base;

/* Pointers to shared_ringbuffers */
ring_handle_t rx_ring;
ring_handle_t tx_ring;

static int internal_is_tx_fifo_busy(
    meson_uart_regs_t *regs)
{
    /* check the TXFE (transmit buffer FIFO empty) flag, which is cleared
     * automatically when data is written to the TxFIFO. Even though the flag
     * is set, the actual data transmission via the UART's 32 byte FIFO buffer
     * might still be in progress.
     */
    return (0 == (regs->sr & AML_UART_TX_EMPTY));
}

/* TODO - Fix setting baud rate */
static void set_baud(long bps)
{
    /* TODO: Fix buad rate setup */
    
    // meson_uart_regs_t *regs = (meson_uart_regs_t *) uart_base;

    // // Wait to clear transmit port
    // while (internal_is_tx_fifo_busy(regs)) {

    // }

    // // Caluclate baud rate
    // uint32_t val = 0;
    // val = DIV_ROUND_CLOSEST(UART_REF_CLK / 4, bps) - 1;
    // val |= AML_UART_BAUD_USE;

    // regs->reg5 = val;
}


int serial_configure(
    long bps,
    int char_size,
    enum serial_parity parity,
    int stop_bits)
{
    meson_uart_regs_t *regs = (meson_uart_regs_t *) uart_base;
    
    uint32_t cr;
    /* Character size */
    cr = regs->cr;
    if (char_size == 8) {
        cr |= AML_UART_DATA_LEN_8BIT;
    } else if (char_size == 7) {
        cr |= AML_UART_DATA_LEN_7BIT;
    } else {
        return -1;
    }
    /* Stop bits */
    if (stop_bits == 2) {
        cr |= AML_UART_STOP_BIT_2SB;
    } else if (stop_bits == 1) {
        cr |= AML_UART_STOP_BIT_1SB;
    } else {
        return -1;
    }

    /* Parity */
    if (parity == PARITY_NONE) {
        cr &= ~AML_UART_PARITY_EN;
    } else if (parity == PARITY_ODD) {
        /* ODD */
        cr |= AML_UART_PARITY_EN;
        cr |= AML_UART_PARITY_TYPE;
    } else if (parity == PARITY_EVEN) {
        /* Even */
        cr |= AML_UART_PARITY_EN;
        cr &= ~AML_UART_PARITY_TYPE;
    } else {
        return -1;
    }
    /* Apply the changes */
    regs->cr = cr;
    /* Now set the baud rate */
    set_baud(bps);
    return 0;
}

int getchar()
{
    meson_uart_regs_t *regs = (meson_uart_regs_t *) uart_base;

    while (regs->sr & AML_UART_RX_EMPTY);
    return regs->rfifo;
}

// Putchar that is using the hardware FIFO buffers --> Switch to DMA later 
int putchar(int c) {

    meson_uart_regs_t *regs = (meson_uart_regs_t *) uart_base;

    while (regs->sr & AML_UART_TX_FULL);

    /* Add character to the buffer. */
    regs->wfifo = c & 0x7f;
    if (c == '\n') {
        putchar('\r');
    }

    return 0;
}

// Called from handle tx, write each character stored in the buffer to the serial port
static void
raw_tx(char *phys, unsigned int len, void *cookie)
{
    // This is byte by byte for now, switch to DMA use later
    for (int i = 0; i < len || phys[i] != '\0'; i++) {
        // Loop until the fifo queue is ready to transmit
        while (putchar(phys[i]) != 0);
    }
}

void handle_tx() {
    uintptr_t buffer = 0;
    unsigned int len = 0;
    void *cookie = 0;
    // Dequeue something from the Tx ring -> the server will have placed something in here, if its empty then nothing to do
    while (!driver_dequeue(tx_ring.used_ring, &buffer, &len, &cookie)) {
        // Buffer cointaining the bytes to write to serial
        char *phys = (char * )buffer;
        // Handle the tx
        raw_tx(phys, len, cookie);
        // Then enqueue this buffer back into the free queue, so that it can be collected and reused by the server
        enqueue_free(&tx_ring, buffer, len, &cookie);
    }
}


void handle_irq() {
    /* Here we have interrupted because a character has been inputted. We first want to get the 
    character from the hardware FIFO queue.

    Then we want to dequeue from the rx free ring, and populate it, then add to the rx used queue
    ready to be processed by the client server
    */
    int input = getchar();

    // Not sure if we should be printing this here or elsewhere? What is the expected behaviour?
    // putchar(input);

    if (input == -1) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": invalid input when attempting to getchar\n");
        return;
    }

    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0; 

    void *cookie = 0;

    int ret = dequeue_free(&rx_ring, &buffer, &buffer_len, &cookie);

    if (ret != 0) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": unable to dequeue from the rx free ring\n");
        return;
    }

    ((char *) buffer)[0] = (char) input;

    // Now place in the rx used ring
    ret = enqueue_used(&rx_ring, buffer, 1, &cookie);

    if (ret != 0) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": unable to enqueue to the tx free ring\n");
        return;
    }
}

// Init function required by CP for every PD
void init(void) {
    sel4cp_dbg_puts(sel4cp_name);
    sel4cp_dbg_puts(": elf PD init function running\n");

    // Init the shared ring buffers
    ring_init(&rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, 0, SIZE, SIZE);
    ring_init(&tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, 0, SIZE, SIZE);

    meson_uart_regs_t *regs = (meson_uart_regs_t *) uart_base;

    /* Line configuration */
    int ret = serial_configure(115200, 8, PARITY_NONE, 1);

    if (ret != 0) {
        sel4cp_dbg_puts("Error occured during line configuration\n");
    }

    // /* Enable the UART */
    uint32_t val;
    val = regs->cr;
    val |= AML_UART_CLEAR_ERR;
    regs->cr = val;
    val &= ~AML_UART_CLEAR_ERR;
    regs->cr = val;
    val |= (AML_UART_RX_EN | AML_UART_TX_EN);
    regs->cr = val;
    val |= (AML_UART_RX_INT_EN);
    regs->cr = val;
    val = (AML_UART_RECV_IRQ(1));
    regs->irqc = val;
}

// Entry point that is invoked on a serial interrupt, or notifications from the server using the TX and RX channels
void notified(sel4cp_channel ch) {
    sel4cp_dbg_puts(sel4cp_name);
    sel4cp_dbg_puts(": elf PD notified function running\n");

    switch(ch) {
        case IRQ_CH:
            handle_irq();
            sel4cp_irq_ack(ch);
            sel4cp_notify(RX_CH);
            return;
        case TX_CH:
            handle_tx();
            break;
        case RX_CH:
            break;
        default:
            sel4cp_dbg_puts("serial driver: received notification on unexpected channel\n");
            break;
    }
}