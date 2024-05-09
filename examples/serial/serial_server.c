#include <ctype.h>
#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>
#include <serial_config.h>

#define TX_CH 0
#define RX_CH 1

uintptr_t rx_queue;
uintptr_t tx_queue;

uintptr_t rx_data;
uintptr_t tx_data;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

uint32_t local_head;
uint32_t local_tail;

bool repl;

void _sddf_putchar(char c)
{
    if (serial_queue_full(&tx_queue_handle, local_tail)
            || (serial_queue_full(&tx_queue_handle, local_tail + 1)
                && c != '\n')) {
        return;
    }

    serial_enqueue(&tx_queue_handle, (char *)tx_data, &local_tail, c);

    /* Make changes visible to virtualiser if character is flush */
    if (repl || c == '\n') {
        serial_update_visible_tail(&tx_queue_handle, local_tail);
        if (serial_require_producer_signal(&tx_queue_handle)) {
            serial_cancel_producer_signal(&tx_queue_handle);
            microkit_notify(TX_CH);
        }
    }
}

void init(void)
{
    serial_cli_queue_init_sys(microkit_name, &rx_queue_handle, rx_queue, &tx_queue_handle, tx_queue);
    sddf_printf("Hello world! I am %s.\nPlease give me character!\n", microkit_name);
}

void notified(microkit_channel ch)
{
    bool reprocess = true;
    repl = true;
    char c[2] = {0};
    while (reprocess) {
        while (!serial_dequeue(&rx_queue_handle, (char *)rx_data, &rx_queue_handle.queue->head, c)) {
            if (c[0] == '\n') {
                sddf_printf("\\n");
            } else {
                sddf_printf((const char *)&c);
            }
        }

        serial_request_producer_signal(&rx_queue_handle);
        reprocess = false;

        if (!serial_queue_empty(&rx_queue_handle, rx_queue_handle.queue->head)) {
            serial_cancel_producer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }

    repl = false;
}
