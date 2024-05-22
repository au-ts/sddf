#include <ctype.h>
#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>
#include <serial_config.h>

#define TX_CH 0
#define RX_CH 1

serial_queue_t *rx_queue;
serial_queue_t *tx_queue;

char *rx_data;
char *tx_data;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

uint32_t local_head;

void init(void)
{
    serial_cli_queue_init_sys(microkit_name, &rx_queue_handle, rx_queue, rx_data, &tx_queue_handle, tx_queue, tx_data);
    serial_putchar_init(TX_CH, &tx_queue_handle);
    sddf_printf("Hello world! I am %s.\r\nPlease give me character!\r\n", microkit_name);
}

void notified(microkit_channel ch)
{
    bool reprocess = true;
    char c[2] = {0};
    while (reprocess) {
        while (!serial_dequeue(&rx_queue_handle, &rx_queue_handle.queue->head, c)) {
            if (c[0] == '\r') {
                sddf_putchar_repl('\\');
                sddf_putchar_repl('r');
            } else {
                sddf_putchar_repl(c[0]);
            }
        }

        serial_request_producer_signal(&rx_queue_handle);
        reprocess = false;

        if (!serial_queue_empty(&rx_queue_handle, rx_queue_handle.queue->head)) {
            serial_cancel_producer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }
}
