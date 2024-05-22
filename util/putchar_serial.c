#include <microkit.h>
#include <sddf/serial/queue.h>

#include <sddf/util/printf.h>

static microkit_channel tx_ch;
static serial_queue_handle_t *tx_queue_handle;

static uint32_t local_tail;

/* Ensure to call serial_putchar_init during initialisation. Multiplexes output based on \n or when buffer is full. */
void _sddf_putchar(char c)
{
    if (serial_queue_full(tx_queue_handle, local_tail)) {
        return;
    }

    serial_enqueue(tx_queue_handle, &local_tail, c);

    /* Make changes visible to virtualiser if character is flush or if queue is now filled */
    if (serial_queue_full(tx_queue_handle, local_tail) || c == '\n') {
        serial_update_visible_tail(tx_queue_handle, local_tail);
        if (serial_require_producer_signal(tx_queue_handle)) {
            serial_cancel_producer_signal(tx_queue_handle);
            microkit_notify(tx_ch);
        }
    }
}

void sddf_putchar_repl(char c)
{
    if (serial_queue_full(tx_queue_handle, local_tail)) {
        return;
    }

    serial_enqueue(tx_queue_handle, &local_tail, c);

    serial_update_visible_tail(tx_queue_handle, local_tail);
    if (serial_require_producer_signal(tx_queue_handle)) {
        serial_cancel_producer_signal(tx_queue_handle);
        microkit_notify(tx_ch);
    }
}

/* Initialise the serial putchar library. */
void serial_putchar_init(microkit_channel serial_tx_ch, serial_queue_handle_t *serial_tx_queue_handle)
{
    tx_ch = serial_tx_ch;
    tx_queue_handle = serial_tx_queue_handle;
    local_tail = serial_tx_queue_handle->queue->tail;
}