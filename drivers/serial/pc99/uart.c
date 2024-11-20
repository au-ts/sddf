#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <serial_config.h>

#define IOPORT_ID 0
#define IOPORT_BASE 0x3f8

/*
 * Port offsets
 * W    - write
 * R    - read
 * RW   - read and write
 * DLAB - Alternate register function bit
 */

#define SERIAL_THR  0 /* Transmitter Holding Buffer (W ) DLAB = 0 */
#define SERIAL_RBR  0 /* Receiver Buffer            (R ) DLAB = 0 */
#define SERIAL_DLL  0 /* Divisor Latch Low Byte     (RW) DLAB = 1 */
#define SERIAL_IER  1 /* Interrupt Enable Register  (RW) DLAB = 0 */
#define SERIAL_DLH  1 /* Divisor Latch High Byte    (RW) DLAB = 1 */
#define SERIAL_IIR  2 /* Interrupt Identification   (R ) */
#define SERIAL_FCR  2 /* FIFO Control Register      (W ) */
#define SERIAL_LCR  3 /* Line Control Register      (RW) */
#define SERIAL_MCR  4 /* Modem Control Register     (RW) */
#define SERIAL_LSR  5 /* Line Status Register       (R ) */
#define SERIAL_MSR  6 /* Modem Status Register      (R ) */
#define SERIAL_SR   7 /* Scratch Register           (RW) */
#define SERIAL_DLAB BIT(7)
#define SERIAL_LSR_DATA_READY BIT(0)
#define SERIAL_LSR_TRANSMITTER_EMPTY BIT(5)

#define TX_CH  1

serial_queue_t *tx_queue = (serial_queue_t *)0x4001000;
char *tx_data = (char *)0x4002000;
serial_queue_handle_t tx_queue_handle;

void write(uint16_t port_offset, uint8_t v)
{
    microkit_x86_ioport_write_8(IOPORT_ID, IOPORT_BASE + port_offset, v);
}

uint8_t read(uint16_t port_offset)
{
    return microkit_x86_ioport_read_8(IOPORT_ID, IOPORT_BASE + port_offset);
}

int ready(void)
{
    return read(SERIAL_LSR) & SERIAL_LSR_TRANSMITTER_EMPTY;
}

void init(void)
{
    while (!(read(SERIAL_LSR) & 0x60)); /* wait until not busy */

    write(SERIAL_LCR, 0x00);
    write(SERIAL_IER, 0x00); /* disable generating interrupts */
    write(SERIAL_LCR, 0x80); /* line control register: command: set divisor */
    write(SERIAL_DLL, 0x01); /* set low byte of divisor to 0x01 = 115200 baud */
    write(SERIAL_DLH, 0x00); /* set high byte of divisor to 0x00 */
    write(SERIAL_LCR, 0x03); /* line control register: set 8 bit, no parity, 1 stop bit */
    write(SERIAL_MCR, 0x0b); /* modem control register: set DTR/RTS/OUT2 */

    read(SERIAL_RBR); /* clear receiver port */
    read(SERIAL_LSR); /* clear line status port */
    read(SERIAL_MSR); /* clear modem status port */

    serial_queue_init(&tx_queue_handle, tx_queue, SERIAL_TX_DATA_REGION_CAPACITY_DRIV, tx_data);
}

static void tx_provide(void)
{
    bool transferred = false;
    char c;
    while (!serial_queue_empty(&tx_queue_handle, tx_queue_handle.queue->head)) {
        serial_dequeue(&tx_queue_handle, &tx_queue_handle.queue->head, &c);
        while (!ready());
        write(SERIAL_THR, c);
        transferred = true;
    }

    serial_request_producer_signal(&tx_queue_handle);

    if (transferred && serial_require_consumer_signal(&tx_queue_handle)) {
        serial_cancel_consumer_signal(&tx_queue_handle);
        microkit_notify(TX_CH);
    }
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case TX_CH:
        tx_provide();
        break;
    default:
        sddf_dprintf("UART|LOG: received notification on unexpected channel: %u\n", ch);
        break;
    }
}
