#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/serial/queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>
#include <serial_config.h>

#define DRIVER 0
#define CLIENT_CH 1

uintptr_t tx_free_drv;
uintptr_t tx_active_drv;
uintptr_t tx_free_cli0;
uintptr_t tx_active_cli0;
uintptr_t tx_free_cli1;
uintptr_t tx_active_cli1;

uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli1_vaddr;

uintptr_t buffer_data_region_cli0_paddr;
uintptr_t buffer_data_region_cli1_paddr;

#define SERIAL_TX_CH 3

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;

#define BENCH_FINISH_IN 20
#define BENCH_FINISH_OUT 21

typedef struct state {
    net_queue_handle_t tx_queue_drv;
    net_queue_handle_t tx_queue_clients[NUM_NETWORK_CLIENTS];
    uintptr_t buffer_region_vaddrs[NUM_NETWORK_CLIENTS];
    uintptr_t buffer_region_paddrs[NUM_NETWORK_CLIENTS];
} state_t;

state_t state;

int extract_offset(uintptr_t *phys)
{
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (*phys >= state.buffer_region_paddrs[client] &&
            *phys < state.buffer_region_paddrs[client] + state.tx_queue_clients[client].size * NET_BUFFER_SIZE) {
            *phys = *phys - state.buffer_region_paddrs[client];
            return client;
        }
    }
    return -1;
}

uint64_t tx_tot = 0;
uint64_t tx_num = 0;
uint64_t tx_min = UINT64_MAX;
uint64_t tx_max = 0;

void tx_provide()
{
    uint64_t tx_tot_local = 0;
    bool enqueued = false;
    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!net_queue_empty_active(&state.tx_queue_clients[client])) {
                net_buff_desc_t buffer;
                int err = net_dequeue_active(&state.tx_queue_clients[client], &buffer);
                assert(!err);
                tx_tot_local++;

                if (buffer.io_or_offset % NET_BUFFER_SIZE ||
                    buffer.io_or_offset >= NET_BUFFER_SIZE * state.tx_queue_clients[client].size) {
                    sddf_dprintf("VIRT_TX|LOG: Client provided offset %lx which is not buffer aligned or outside of buffer region\n",
                                 buffer.io_or_offset);
                    err = net_enqueue_free(&state.tx_queue_clients[client], buffer);
                    assert(!err);
                    continue;
                }

                cache_clean(buffer.io_or_offset + state.buffer_region_vaddrs[client],
                            buffer.io_or_offset + state.buffer_region_vaddrs[client] + buffer.len);

                buffer.io_or_offset = buffer.io_or_offset + state.buffer_region_paddrs[client];
                err = net_enqueue_active(&state.tx_queue_drv, buffer);
                assert(!err);
                enqueued = true;
            }

            net_request_signal_active(&state.tx_queue_clients[client]);
            reprocess = false;

            if (!net_queue_empty_active(&state.tx_queue_clients[client])) {
                net_cancel_signal_active(&state.tx_queue_clients[client]);
                reprocess = true;
            }
        }
    }

    if (enqueued && net_require_signal_active(&state.tx_queue_drv)) {
        net_cancel_signal_active(&state.tx_queue_drv);
        microkit_notify_delayed(DRIVER);
    }
    
    tx_num++;
    tx_tot += tx_tot_local;
    if (tx_tot_local > tx_max) tx_max = tx_tot_local;
    if (tx_tot_local < tx_min) tx_min = tx_tot_local; 
}

uint64_t rx_tot = 0;
uint64_t rx_num = 0;
uint64_t rx_min = UINT64_MAX;
uint64_t rx_max = 0;

void tx_return()
{
    uint64_t rx_tot_local = 0;
    bool reprocess = true;
    bool notify_clients[NUM_NETWORK_CLIENTS] = {false};
    while (reprocess) {
        while (!net_queue_empty_free(&state.tx_queue_drv)) {
            net_buff_desc_t buffer;
            int err = net_dequeue_free(&state.tx_queue_drv, &buffer);
            assert(!err);
            rx_tot_local++;

            int client = extract_offset(&buffer.io_or_offset);
            assert(client >= 0);

            err = net_enqueue_free(&state.tx_queue_clients[client], buffer);
            assert(!err);
            notify_clients[client] = true;
        }

        net_request_signal_free(&state.tx_queue_drv);
        reprocess = false;

        if (!net_queue_empty_free(&state.tx_queue_drv)) {
            net_cancel_signal_free(&state.tx_queue_drv);
            reprocess = true;
        }
    }

    for (int client = 0; client < NUM_NETWORK_CLIENTS; client++) {
        if (notify_clients[client] && net_require_signal_free(&state.tx_queue_clients[client])) {
            net_cancel_signal_free(&state.tx_queue_clients[client]);
            microkit_notify(client + CLIENT_CH);
        }
    }

    rx_num++;
    rx_tot += rx_tot_local;
    if (rx_tot_local > rx_max) rx_max = rx_tot_local;
    if (rx_tot_local < rx_min) rx_min = rx_tot_local;
}

void notified(microkit_channel ch)
{
    if (ch != BENCH_FINISH_IN) {
        tx_return();
        tx_provide(); 
    }
    else {
        sddf_printf("VIRT TX Return Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", rx_tot/rx_num, rx_min, rx_max);
        sddf_printf("VIRT TX Provide Batch Values| Avg: %lu, Min: %lu, Max: %lu\n", tx_tot/tx_num, tx_min, tx_max);
        rx_tot = 0;
        rx_num = 0;
        rx_min = UINT64_MAX;
        rx_max = 0;
        tx_tot = 0;
        tx_num = 0;
        tx_min = UINT64_MAX;
        tx_max = 0;
        microkit_notify(BENCH_FINISH_OUT);
    }
}

void init(void)
{
    serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue, serial_tx_data);
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);

    net_queue_init(&state.tx_queue_drv, (net_queue_t *)tx_free_drv, (net_queue_t *)tx_active_drv, NET_TX_QUEUE_SIZE_DRIV);
    net_virt_queue_init_sys(microkit_name, state.tx_queue_clients, tx_free_cli0, tx_active_cli0);

    net_mem_region_init_sys(microkit_name, state.buffer_region_vaddrs, buffer_data_region_cli0_vaddr);

    /* CDTODO: Can we make this system agnostic? */
    state.buffer_region_paddrs[0] = buffer_data_region_cli0_paddr;
    state.buffer_region_paddrs[1] = buffer_data_region_cli1_paddr;

    tx_provide();
}
