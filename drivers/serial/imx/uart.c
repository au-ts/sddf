/*
* Sample serial driver for imx8mm based on the sDDF
*/

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sel4/sel4.h>
#include <serial_config.h>
#include "uart.h"
#include "uart_config.h"

#define BIT(nr) (1UL << (nr))

// Defines to manage interrupts and notifications
#define IRQ_CH 0
#define TX_CH  1
#define RX_CH  2

/* Memory regions. These all have to be here to keep compiler happy */
// Queue components
uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;
uintptr_t shared_dma_paddr;
uintptr_t shared_dma_rx_drv;
// Base of the uart registers
uintptr_t uart_base;

/* Handles for queue structures */
serial_queue_handle_t rx_queue;
serial_queue_handle_t tx_queue;

// Global serial driver state
struct serial_driver global_serial_driver = {0};

/*
 * BaudRate = RefFreq / (16 * (BMR + 1)/(BIR + 1) )
 * BMR and BIR are 16 bit
 * Function taken from seL4 util_libs serial.c implementation for imx8mm
 */
static void imx_uart_set_baud(long bps)
{
    volatile imx_uart_regs_t *regs = (imx_uart_regs_t *) uart_base;

    uint32_t bmr, bir, fcr;
    fcr = regs->fcr;
    fcr &= ~UART_FCR_RFDIV_MASK;
    fcr |= UART_FCR_RFDIV(4);
    bir = 0xf;
    bmr = UART_REF_CLK / bps - 1;
    regs->bir = bir;
    regs->bmr = bmr;
    regs->fcr = fcr;
}

static int internal_is_tx_fifo_busy(
    imx_uart_regs_t *regs)
{
    /* check the TXFE (transmit buffer FIFO empty) flag, which is cleared
     * automatically when data is written to the TxFIFO. Even though the flag
     * is set, the actual data transmission via the UART's 32 byte FIFO buffer
     * might still be in progress.
     */
    return (0 == (regs->sr2 & UART_SR2_TXFIFO_EMPTY));
}

int serial_configure(
    long bps,
    int char_size,
    enum serial_parity parity,
    int stop_bits, 
    int mode, 
    int echo)
{
    volatile imx_uart_regs_t *regs = (imx_uart_regs_t *) uart_base;
    global_serial_driver.mode = mode;
    global_serial_driver.echo = echo;

    uint32_t cr2;
    /* Character size */
    cr2 = regs->cr2;
    if (char_size == 8) {
        cr2 |= UART_CR2_WS;
    } else if (char_size == 7) {
        cr2 &= ~UART_CR2_WS;
    } else {
        return -1;
    }
    /* Stop bits */
    if (stop_bits == 2) {
        cr2 |= UART_CR2_STPB;
    } else if (stop_bits == 1) {
        cr2 &= ~UART_CR2_STPB;
    } else {
        return -1;
    }
    /* Parity */
    if (parity == PARITY_NONE) {
        cr2 &= ~UART_CR2_PREN;
    } else if (parity == PARITY_ODD) {
        /* ODD */
        cr2 |= UART_CR2_PREN;
        cr2 |= UART_CR2_PROE;
    } else if (parity == PARITY_EVEN) {
        /* Even */
        cr2 |= UART_CR2_PREN;
        cr2 &= ~UART_CR2_PROE;
    } else {
        return -1;
    }
    /* Apply the changes */
    regs->cr2 = cr2;
    // microkit_dbg_puts("finished configuring the line, setting the baud rate\n");
    /* Now set the board rate */
    imx_uart_set_baud(bps);
    return 0;
}

int getchar()
{
    volatile imx_uart_regs_t *regs = (imx_uart_regs_t *) uart_base;
    uint32_t reg = 0;
    int c = -1;

    if (regs->sr2 & UART_SR2_RXFIFO_RDR) {
        reg = regs->rxd;
        if (reg & UART_URXD_READY_MASK) {
            c = reg & UART_BYTE_MASK;
        }
    }
    return c;
}

// Putchar that is using the hardware FIFO buffers --> Switch to DMA later 
int putchar(int c) {

    volatile imx_uart_regs_t *regs = (imx_uart_regs_t *) uart_base;

    if (internal_is_tx_fifo_busy(regs)) {
        // A transmit is probably in progress, we will have to wait
        return -1;
    }

    if (c == '\n') {
        // For now, by default we will have Auto-send CR(Carriage Return) enabled
        /* write CR first */
        regs->txd = '\r';
        /* if we transform a '\n' (LF) into '\r\n' (CR+LF) this shall become an
         * atom, ie we don't want CR to be sent and then fail at sending LF
         * because the TX FIFO is full. Basically there are two options:
         *   - check if the FIFO can hold CR+LF and either send both or none
         *   - send CR, then block until the FIFO has space and send LF.
         * Assuming that if SERIAL_AUTO_CR is set, it's likely this is a serial
         * console for logging, so blocking seems acceptable in this special
         * case. The IMX6's TX FIFO size is 32 byte and TXFIFO_EMPTY is cleared
         * automatically as soon as data is written from regs->txd into the
         * FIFO. Thus the worst case blocking is roughly the time it takes to
         * send 1 byte to have room in the FIFO again. At 115200 baud with 8N1
         * this takes 10 bit-times, which is 10/115200 = 86,8 usec.
         */
        while (internal_is_tx_fifo_busy(regs)) {
            /* busy loop */
        }
    }

    regs->txd = c;

    return 0;
}

// Called from handle tx, write each character stored in the buffer to the serial port
static void
raw_tx(char *phys, unsigned int len)
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
    // Dequeue something from the Tx queue -> the server will have placed something in here, if its empty then nothing to do
    while (!serial_dequeue_active(&tx_queue, &buffer, &len)) {
        // Buffer cointaining the bytes to write to serial
        char *phys = (char * )buffer;
        // Handle the tx
        raw_tx(phys, len);
        // Then enqueue this buffer back into the free queue, so that it can be collected and reused by the server
        serial_enqueue_free(&tx_queue, buffer, len);
    }
}


void handle_irq() {
    /* Here we have interrupted because a character has been inputted. We first want to get the
    character from the hardware FIFO queue.
    Then we want to dequeue from the rx free queue, and populate it, then add to the rx active queue
    ready to be processed by the client server
    */
    int input = getchar();
    char input_char = (char) input;
    microkit_irq_ack(IRQ_CH);

    if (input == -1) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": invalid input when attempting to getchar\n");
        return;
    }

    int ret = 0;

    if (global_serial_driver.echo == ECHO_EN) {
        // // Special case for backspace
        if (input_char == '\b' || input_char == 0x7f) {
            // Backspace will move the cursor back, and space will erase the character
            putchar('\b');
            putchar(' ');
            putchar('\b');
        } else if (input_char == '\r') {
            // Convert the carriage return to a new line
            putchar('\n');
        }
        else {
            putchar(input);
        }
    }

    if (global_serial_driver.mode == RAW_MODE) {
        // Place characters straight into the buffer

        // Address that we will pass to dequeue to store the buffer address
        uintptr_t buffer = 0;
        // Integer to store the length of the buffer
        unsigned int buffer_len = 0;

        ret = serial_dequeue_free(&rx_queue, &buffer, &buffer_len);

        if (ret != 0) {
            microkit_dbg_puts(microkit_name);
            microkit_dbg_puts(": unable to dequeue from the rx free queue\n");
            return;
        }

        ((char *) buffer)[0] = (char) input;

        // Now place in the rx active queue
        ret = serial_enqueue_active(&rx_queue, buffer, 1);
        microkit_notify(RX_CH);

    } else if (global_serial_driver.mode == LINE_MODE) {
        // Place in a buffer, until we reach a new line, ctrl+d/ctrl+c/enter (check what else can stop)
        if (global_serial_driver.line_buffer == 0) {
            // We need to dequeue a buffer to use
            // Address that we will pass to dequeue to store the buffer address
            uintptr_t buffer = 0;
            // Integer to store the length of the buffer
            unsigned int buffer_len = 0; 

            ret = serial_dequeue_free(&rx_queue, &buffer, &buffer_len);
            if (ret != 0) {
                microkit_dbg_puts(microkit_name);
                microkit_dbg_puts(": unable to dequeue from the rx free queue\n");
                return;
            }

            global_serial_driver.line_buffer = buffer;
            global_serial_driver.line_buffer_size = 0;
        } 

        // Check that the buffer is not full, and other exit conditions here
        if (global_serial_driver.line_buffer_size > BUFFER_SIZE ||
            input_char == EOT || 
            input_char == ETX || 
            input_char == LF ||
            input_char == SB ||
            input_char == CR) {
                char *char_arr = (char * ) global_serial_driver.line_buffer;
                // Place the line end character into buffer
                char_arr[global_serial_driver.line_buffer_size] = input_char;
                global_serial_driver.line_buffer_size += 1;
                // Enqueue buffer back
                ret = serial_enqueue_active(&rx_queue, global_serial_driver.line_buffer, global_serial_driver.line_buffer_size);
                // Zero out the driver states
                global_serial_driver.line_buffer = 0;
                global_serial_driver.line_buffer_size = 0;
                microkit_notify(RX_CH);

        } else {
            // Otherwise, add to the character array
            char *char_arr = (char * ) global_serial_driver.line_buffer;
            // Conduct any line editing as long as we have stuff in the buffer
            if (input_char == 0x7f && global_serial_driver.line_buffer_size > 0) {
                // Remove last character
                global_serial_driver.line_buffer_size -= 1;
                char_arr[global_serial_driver.line_buffer_size] = 0;
            } else {
                char_arr[global_serial_driver.line_buffer_size] = input;
                global_serial_driver.line_buffer_size += 1;
            }
        }
    }



    if (ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": unable to enqueue to the tx free queue\n");
        return;
    }
}

// Init function required by CP for every PD
void init(void) {
    microkit_dbg_puts(microkit_name);
    microkit_dbg_puts(": elf PD init function running\n");

    // Init the shared queues
    serial_queue_init(&rx_queue, (serial_queue_t *)rx_free, (serial_queue_t *)rx_active, RX_QUEUE_SIZE_DRIV);
    serial_queue_init(&tx_queue, (serial_queue_t *)tx_free, (serial_queue_t *)tx_active, TX_QUEUE_SIZE_DRIV);

    volatile imx_uart_regs_t *regs = (imx_uart_regs_t *) uart_base;

    /* Line configuration. Set LINE or RAW mode here, and disable or enable ECHO */
    int ret = serial_configure(115200, 8, PARITY_NONE, 1, UART_MODE, ECHO_MODE);

    if (ret != 0) {
        microkit_dbg_puts("Error occured during line configuration\n");
    }

    /* Enable the UART */
    regs->cr1 |= UART_CR1_UARTEN;                /* Enable The uart.                  */
    regs->cr2 |= UART_CR2_RXEN | UART_CR2_TXEN;  /* RX/TX enable                      */
    regs->cr2 |= UART_CR2_IRTS;                  /* Ignore RTS                        */
    regs->cr3 |= UART_CR3_RXDMUXDEL;             /* Configure the RX MUX              */
    /* Initialise the receiver interrupt.                                             */
    regs->cr1 &= ~UART_CR1_RRDYEN;               /* Disable recv interrupt.           */
    regs->fcr &= ~UART_FCR_RXTL_MASK;            /* Clear the rx trigger level value. */
    regs->fcr |= UART_FCR_RXTL(1);               /* Set the rx tigger level to 1.     */
    regs->cr1 |= UART_CR1_RRDYEN;                /* Enable recv interrupt.            */
}

// Entry point that is invoked on a serial interrupt, or notifications from the server using the TX and RX channels
void notified(microkit_channel ch) {
    switch(ch) {
        case IRQ_CH:
            handle_irq();
            return;
        case TX_CH:
            handle_tx();
            break;
        case RX_CH:
            break;
        default:
            microkit_dbg_puts("serial driver: received notification on unexpected channel\n");
            break;
    }
}