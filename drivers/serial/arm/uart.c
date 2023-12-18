#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include "uart.h"
#include "uart_config.h"
#include <sddf/serial/shared_ringbuffer.h>

/*
 * The PL011 is supposedly universal, which means that this driver should be
 * usable for any PL011 compatible device.
 * Right now the driver is making assumptions that are true on QEMU, but not
 * necessarily on hardware. Once this is fixed then this is a proper PL011
 * driver.
 */

#define LOG_DRIVER(...) do{ microkit_dbg_puts(microkit_name); microkit_dbg_puts("|INFO: "); microkit_dbg_puts(__VA_ARGS__); }while(0)
#define LOG_DRIVER_ERR(...) do{ microkit_dbg_puts(microkit_name); microkit_dbg_puts("|ERROR: "); microkit_dbg_puts(__VA_ARGS__); }while(0)

/* Defines to manage interrupts and notifications */
#define IRQ_CH 1
#define TX_CH  8
#define RX_CH  10

/* Shared ring buffers */
uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;
/* UART device registers */
uintptr_t uart_base;

/* Handlers to be given to the shared ringbuffer API */
ring_handle_t rx_ring;
ring_handle_t tx_ring;

struct serial_driver global_serial_driver = {0};

int getchar() {
    volatile struct pl011_uart_regs *regs = (volatile struct pl011_uart_regs *) uart_base;
    // @ivanv: don't like having an infinite loop here
    while (regs->fr & PL011_UARTFR_RXFE) {};

    return regs->dr;
}

int putchar(int ch) {
    volatile struct pl011_uart_regs *regs = (volatile struct pl011_uart_regs *) uart_base;

    while ((regs->fr & PL011_UARTFR_TXFF) != 0) {};

    regs->dr = ch;
    // @ivanv: figure out
    // if (ch == '\r') {
    //     putchar('\n');
    // }

    return 0;
}

// Called from handle tx, write each character stored in the buffer to the serial port
static void raw_tx(char *phys, unsigned int len, void *cookie) {
    // This is byte by byte for now, switch to DMA use later
    for (int i = 0; i < len && phys[i] != '\0'; i++) {
        // Loop until the fifo queue is ready to transmit
        // @ivanv: putchar always returns zero? what's the point of the return value
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
    char input_char = (char) input;
    microkit_irq_ack(IRQ_CH);

    // Not sure if we should be printing this here or elsewhere? What is the expected behaviour?
    // putchar(input);

    if (input == -1) {
        LOG_DRIVER_ERR("invalid input when attempting to getchar\n");
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

        void *cookie = 0;

        ret = dequeue_free(&rx_ring, &buffer, &buffer_len, &cookie);

        if (ret != 0) {
            LOG_DRIVER_ERR("unable to dequeue from RX free ring\n");
            return;
        }

        ((char *) buffer)[0] = (char) input;

        // Now place in the rx used ring
        ret = enqueue_used(&rx_ring, buffer, 1, &cookie);
        microkit_notify(RX_CH);

    } else if (global_serial_driver.mode == LINE_MODE) {
        // Place in a buffer, until we reach a new line, ctrl+d/ctrl+c/enter (check what else can stop)
        if (global_serial_driver.line_buffer == 0) {
            // We need to dequeue a buffer to use
            // Address that we will pass to dequeue to store the buffer address
            uintptr_t buffer = 0;
            // Integer to store the length of the buffer
            unsigned int buffer_len = 0;

            void *cookie = 0;

            ret = dequeue_free(&rx_ring, &buffer, &buffer_len, &cookie);
            if (ret != 0) {
                LOG_DRIVER_ERR("unable to dequeue from the RX free ring\n");
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
                void *cookie = 0;
                // Place the line end character into buffer
                char_arr[global_serial_driver.line_buffer_size] = input_char;
                global_serial_driver.line_buffer_size += 1;
                // Enqueue buffer back
                ret = enqueue_used(&rx_ring, global_serial_driver.line_buffer, global_serial_driver.line_buffer_size, &cookie);
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
        LOG_DRIVER_ERR("unable to enqueue to the TX free ring\n");
        return;
    }
}

void init(void) {
    LOG_DRIVER("initialising\n");

    // Init the shared ring buffers
    ring_init(&rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, 0, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, 0, NUM_BUFFERS, NUM_BUFFERS);

    volatile struct pl011_uart_regs *regs = (volatile struct pl011_uart_regs *) uart_base;
    // @ivanv what does 0x50 mean!
    regs->imsc = 0x50;

    // @ivanv: need to do proper initialisation

    /* Line configuration. Set LINE or RAW mode here, and disable or enable ECHO */
    // int ret = serial_configure(115200, 8, PARITY_NONE, 1, UART_MODE, ECHO_MODE);

    // if (ret != 0) {
    //     LOG_DRIVER("error occured during line configuration\n");
    // }
}

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
            LOG_DRIVER("received notification on unexpected channel\n");
            break;
    }
}
