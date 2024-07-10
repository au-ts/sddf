#include <string.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/serial/queue.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>
#include <serial_config.h>

#define VIRT_RX_CH 0
#define CLIENT_CH 1

net_queue_handle_t rx_queue_virt;
net_queue_handle_t rx_queue_cli;

uintptr_t rx_free_virt;
uintptr_t rx_active_virt;
uintptr_t rx_free_cli;
uintptr_t rx_active_cli;

uintptr_t virt_buffer_data_region;
uintptr_t cli_buffer_data_region;

#define SERIAL_TX_CH 3

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;

#define BENCH_FINISH_IN 20
#define BENCH_FINISH_OUT 21

uint64_t rx_tot = 0;
uint64_t rx_num = 0;
uint64_t rx_min = UINT64_MAX;
uint64_t rx_max = 0;

void rx_return(void)
{
    uint64_t rx_tot_local = 0;
    bool enqueued = false;
    bool reprocess = true;

    while (reprocess) {
        while (!net_queue_empty_active(&rx_queue_virt) && !net_queue_empty_free(&rx_queue_cli)) {
            net_buff_desc_t cli_buffer, virt_buffer = {0};
            int err = net_dequeue_free(&rx_queue_cli, &cli_buffer);
            assert(!err);

            if (cli_buffer.io_or_offset % NET_BUFFER_SIZE || cli_buffer.io_or_offset >= NET_BUFFER_SIZE * rx_queue_cli.size) {
                sddf_dprintf("COPY|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
                             cli_buffer.io_or_offset);
                continue;
            }
            rx_tot_local++;

            err = net_dequeue_active(&rx_queue_virt, &virt_buffer);
            assert(!err);

            uintptr_t cli_addr = cli_buffer_data_region + cli_buffer.io_or_offset;
            uintptr_t virt_addr = virt_buffer_data_region + virt_buffer.io_or_offset;

            memcpy((void *)cli_addr, (void *)virt_addr, virt_buffer.len);
            cli_buffer.len = virt_buffer.len;
            virt_buffer.len = 0;

            err = net_enqueue_active(&rx_queue_cli, cli_buffer);
            assert(!err);

            err = net_enqueue_free(&rx_queue_virt, virt_buffer);
            assert(!err);

            enqueued = true;
        }

        net_request_signal_active(&rx_queue_virt);

        /* Only request signal from client if incoming packets from multiplexer are awaiting free buffers */
        if (!net_queue_empty_active(&rx_queue_virt)) {
            net_request_signal_free(&rx_queue_cli);
        } else {
            net_cancel_signal_free(&rx_queue_cli);
        }

        reprocess = false;

        if (!net_queue_empty_active(&rx_queue_virt) && !net_queue_empty_free(&rx_queue_cli)) {
            net_cancel_signal_active(&rx_queue_virt);
            net_cancel_signal_free(&rx_queue_cli);
            reprocess = true;
        }
    }

    if (enqueued && net_require_signal_active(&rx_queue_cli)) {
        net_cancel_signal_active(&rx_queue_cli);
        microkit_notify(CLIENT_CH);
    }

    if (enqueued && net_require_signal_free(&rx_queue_virt)) {
        net_cancel_signal_free(&rx_queue_virt);
        microkit_notify_delayed(VIRT_RX_CH);
    }

    rx_num++;
    rx_tot += rx_tot_local;
    if (rx_tot_local > rx_max) rx_max = rx_tot_local;
    if (rx_tot_local < rx_min) rx_min = rx_tot_local;
}

void notified(microkit_channel ch)
{
    if (ch != BENCH_FINISH_IN) rx_return();
    else {
        sddf_printf("COPY Rx Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", rx_tot/rx_num, rx_min, rx_max);
        rx_tot = 0;
        rx_num = 0;
        rx_min = UINT64_MAX;
        rx_max = 0;
        microkit_notify(BENCH_FINISH_OUT);
    }
}

void init(void)
{
    serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue, serial_tx_data);
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);

    net_copy_queue_init_sys(microkit_name, &rx_queue_cli, rx_free_cli, rx_active_cli, &rx_queue_virt, rx_free_virt,
                            rx_active_virt);
    net_buffers_init(&rx_queue_cli, 0);
}
