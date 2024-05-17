#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/util/util.h>

#define LOG_DRIVER(...) do{ microkit_dbg_puts(microkit_name); microkit_dbg_puts("|INFO: "); microkit_dbg_puts(__VA_ARGS__); }while(0)
#define LOG_DRIVER_ERR(...) do{ microkit_dbg_puts(microkit_name); microkit_dbg_puts("|ERROR: "); microkit_dbg_puts(__VA_ARGS__); }while(0)

/* UART Transmit Holding Register */
#define UART_THR 0x00
/* UART Interrupt Enable Register */
#define UART_IER 0x04
/* Enable Received Data Available Interrupt */
#define UART_IER_ERDAI 0x1
/* UART Line Status Register */
#define UART_LSR 0x14
/* Transmit Holding Register Empty */
#define UART_LSR_THRE 0x20

#define REG_PTR(base, off)     ((volatile uint32_t *)((base) + (off)))

/* Defines to manage interrupts and notifications */
#define IRQ_CH 1
#define TX_CH  8
#define RX_CH  10

/* Shared memory for queues */
uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;
/* UART device registers */
volatile uintptr_t uart_base;

/* Handlers to be given to the queue API */
serial_queue_handle_t rx_queue;
serial_queue_handle_t tx_queue;

int getchar() {
    // TODO: don't check bit zero and use hash define instead
    while (*REG_PTR(uart_base, UART_LSR) & 0x1);

    return *REG_PTR(uart_base, UART_THR);
}

int putchar(int ch) {
    while ((*REG_PTR(uart_base, UART_LSR) & UART_LSR_THRE) == 0);

    /* Add character to the buffer. */
    *REG_PTR(uart_base, UART_THR) = ch;

    return 0;
}

void handle_irq() {
    microkit_irq_ack_delayed(IRQ_CH);

    char input_char = getchar();

    // Special case for backspace
    if (input_char == '\b' || input_char == 0x7f) {
        // Backspace will move the cursor back, and space will erase the character
        putchar('\b');
        putchar(' ');
        putchar('\b');
    } else if (input_char == '\r') {
        // Convert the carriage return to a new line
        putchar('\n');
    } else {
        putchar(input_char);
    }

    // Place characters straight into the buffer
    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0;

    int ret = serial_dequeue_free(&rx_queue, &buffer, &buffer_len);

    if (ret != 0) {
        LOG_DRIVER_ERR("unable to dequeue from RX free queue\n");
        return;
    }

    ((char *) buffer)[0] = input_char;

    // Now place in the rx active queue
    ret = serial_enqueue_active(&rx_queue, buffer, 1);
    microkit_notify(RX_CH);
}

// Called from handle tx, write each character stored in the buffer to the serial port
static void raw_tx(char *phys, unsigned int len) {
    // This is byte by byte for now, switch to DMA use later
    for (int i = 0; i < len && phys[i] != '\0'; i++) {
        // Loop until the fifo queue is ready to transmit
        while (putchar(phys[i]) != 0);
    }
}

void handle_tx() {
    uintptr_t buffer = 0;
    unsigned int len = 0;
    // Dequeue something from the Tx queue -> the virt TX will have placed something in here, if its empty then nothing to do
    while (!serial_dequeue_active(&tx_queue, &buffer, &len)) {
        // Buffer cointaining the bytes to write to serial
        char *phys = (char * )buffer;
        // Handle the tx
        raw_tx(phys, len);
        // Then enqueue this buffer back into the free queue, so that it can be collected and reused by the server
        int err = serial_enqueue_free(&tx_queue, buffer, BUFFER_SIZE);
        assert(!err);
    }
}

void handle_rx() {}

void init(void) {
    LOG_DRIVER("initialising\n");

    // Init the shared queues
    serial_queue_init(&rx_queue, (serial_queue_t *)rx_free, (serial_queue_t *)rx_active, 0, NUM_ENTRIES, NUM_ENTRIES);
    serial_queue_init(&tx_queue, (serial_queue_t *)tx_free, (serial_queue_t *)tx_active, 0, NUM_ENTRIES, NUM_ENTRIES);
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
