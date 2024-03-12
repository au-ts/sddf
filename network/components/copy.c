#include <string.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define MUX_RX_CH 0
#define CLIENT_CH 1

ring_handle_t rx_ring_mux;
ring_handle_t rx_ring_cli;

uintptr_t rx_free_mux;
uintptr_t rx_used_mux;
uintptr_t rx_free_cli;
uintptr_t rx_used_cli;

uintptr_t mux_buffer_data_region;
uintptr_t cli_buffer_data_region;

void rx_return(void)
{
    bool enqueued = false;
    bool reprocess = true;

    while (reprocess) {
        while (!ring_empty(rx_ring_mux.used_ring) && !ring_empty(rx_ring_cli.free_ring)) {
            buff_desc_t cli_buffer, mux_buffer;
            int err = dequeue_free(&rx_ring_cli, &cli_buffer);
            assert(!err);

            if (cli_buffer.phys_or_offset % BUFF_SIZE || cli_buffer.phys_or_offset >= BUFF_SIZE * ((ring_buffer_t *)rx_free_cli)->size) {
                dprintf("COPY|LOG: Client provided offset %llx which is not buffer aligned or outside of buffer region\n", cli_buffer.phys_or_offset);
                continue;
            }

            err = dequeue_used(&rx_ring_mux, &mux_buffer);
            assert(!err);

            uintptr_t cli_addr = cli_buffer_data_region + cli_buffer.phys_or_offset;
            uintptr_t mux_addr = mux_buffer_data_region + mux_buffer.phys_or_offset;

            memcpy((void *)cli_addr, (void *)mux_addr, mux_buffer.len);
            cli_buffer.len = mux_buffer.len;
            mux_buffer.len = 0;
            
            err = enqueue_used(&rx_ring_cli, cli_buffer);
            assert(!err);

            err = enqueue_free(&rx_ring_mux, mux_buffer);
            assert(!err);

            enqueued = true;
        }
        
        request_signal(rx_ring_mux.used_ring);

        /* Only request signal from client if incoming packets from multiplexer are awaiting free buffers */
        if (!ring_empty(rx_ring_mux.used_ring)) request_signal(rx_ring_cli.free_ring);
        else cancel_signal(rx_ring_cli.free_ring);

        reprocess = false;
        
        if (!ring_empty(rx_ring_mux.used_ring) && !ring_empty(rx_ring_cli.free_ring)) {
            cancel_signal(rx_ring_mux.used_ring);
            cancel_signal(rx_ring_cli.free_ring);
            reprocess = true;
        }
    }

    if (enqueued && require_signal(rx_ring_cli.used_ring)) {
        cancel_signal(rx_ring_cli.used_ring);
        microkit_notify(CLIENT_CH);
    }

    if (enqueued && require_signal(rx_ring_mux.free_ring)) {
        cancel_signal(rx_ring_mux.free_ring);
        microkit_notify_delayed(MUX_RX_CH);
    }
}

void notified(microkit_channel ch)
{
    rx_return();
}

void init(void)
{
    copy_ring_init_sys(microkit_name, &rx_ring_cli, rx_free_cli, rx_used_cli, &rx_ring_mux, rx_free_mux, rx_used_mux);
    buffers_init(rx_ring_cli.free_ring, 0, rx_ring_cli.free_ring->size);
}