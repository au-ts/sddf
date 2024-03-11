#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <microkit.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/network/constants.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <system_config.h>

/* Notification channels */
#define DRIVER_CH 0
#define CLIENT_CH 1

/* Ring buffer regions */
uintptr_t rx_free_drv;
uintptr_t rx_used_drv;
uintptr_t rx_free_arp;
uintptr_t rx_used_arp;
uintptr_t rx_free_cli0;
uintptr_t rx_used_cli0;
uintptr_t rx_free_cli1;
uintptr_t rx_used_cli1;

/* Buffer data regions */
uintptr_t buffer_data_vaddr;
uintptr_t buffer_data_paddr;

typedef struct state {
    ring_handle_t rx_ring_drv;
    ring_handle_t rx_ring_clients[NUM_CLIENTS];
    uint8_t mac_addrs[NUM_CLIENTS][ETH_HWADDR_LEN];
} state_t;

state_t state;

/* Boolean to indicate whether a packet has been enqueued into the driver's free ring during notification handling */
static bool notify_drv;

/* Return the client ID if the Mac address is a match. */
int get_client(struct ethernet_header * buffer)
{
    for (int client = 0; client < NUM_CLIENTS; client++) {
        bool match = true;
        for (int i = 0; (i < ETH_HWADDR_LEN) && match; i++) if (buffer->dest.addr[i] != state.mac_addrs[client][i]) match = false;
        if (match) return client;
    }
    return -1;
}

void rx_return(void)
{
    bool reprocess = true;
    bool notify_clients[NUM_CLIENTS] = {false};
    while (reprocess) {
        while (!ring_empty(state.rx_ring_drv.used_ring)) {
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_used(&state.rx_ring_drv, &buffer);
            assert(!err);

            buffer.phys_or_offset = buffer.phys_or_offset - buffer_data_paddr;
            err = seL4_ARM_VSpace_Invalidate_Data(VSPACE_CAP, buffer.phys_or_offset + buffer_data_vaddr, buffer.phys_or_offset + buffer_data_vaddr + buffer.len);
            if (err) dprintf("MUX_RX|ERROR: ARM Vspace invalidate failed\n");
            assert(!err);

            int client = get_client((struct ethernet_header *) (buffer.phys_or_offset + buffer_data_vaddr));
            if (client >= 0) {
                err = enqueue_used(&state.rx_ring_clients[client], buffer);
                assert(!err);
                notify_clients[client] = true;
            } else {
                buffer.phys_or_offset = buffer.phys_or_offset + buffer_data_paddr;
                err = enqueue_free(&state.rx_ring_drv, buffer);
                assert(!err);
                notify_drv = true;
            }
        }

        request_signal(state.rx_ring_drv.used_ring);
        reprocess = false;

        if (!ring_empty(state.rx_ring_drv.used_ring)) {
            cancel_signal(state.rx_ring_drv.used_ring);
            reprocess = true;
        }
    }

    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (notify_clients[client] && require_signal(state.rx_ring_clients[client].used_ring)) {
            cancel_signal(state.rx_ring_clients[client].used_ring);
            microkit_notify(client + CLIENT_CH);
        }
    }    
}

void rx_provide(void)
{
    for (int client = 0; client < NUM_CLIENTS; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!ring_empty(state.rx_ring_clients[client].free_ring)) {
                buff_desc_t buffer;
                int err __attribute__((unused)) = dequeue_free(&state.rx_ring_clients[client], &buffer);
                assert(!err);
                assert(!(buffer.phys_or_offset % BUFF_SIZE) && 
                       (buffer.phys_or_offset < BUFF_SIZE * state.rx_ring_clients[client].free_ring->size));

                buffer.phys_or_offset = buffer.phys_or_offset + buffer_data_paddr;
                err = enqueue_free(&state.rx_ring_drv, buffer);
                assert(!err);
                notify_drv = true;
            }

            request_signal(state.rx_ring_clients[client].free_ring);
            reprocess = false;

            if (!ring_empty(state.rx_ring_clients[client].free_ring)) {
                cancel_signal(state.rx_ring_clients[client].free_ring);
                reprocess = true;
            }
        }
    }

    if (notify_drv && require_signal(state.rx_ring_drv.free_ring)) {
        cancel_signal(state.rx_ring_drv.free_ring);
        microkit_notify(DRIVER_CH);
    }
}

void notified(microkit_channel ch)
{
    rx_return();
    rx_provide();
}

void init(void)
{
    mux_mac_addr_init_sys(microkit_name, (uint8_t *) state.mac_addrs);

    ring_init(&state.rx_ring_drv, (ring_buffer_t *)rx_free_drv, (ring_buffer_t *)rx_used_drv, RX_RING_SIZE_DRIV);
    mux_ring_init_sys(microkit_name, state.rx_ring_clients, rx_free_arp, rx_used_arp);
    buffers_init((ring_buffer_t *)rx_free_drv, buffer_data_paddr, RX_RING_SIZE_DRIV);

    if (require_signal(state.rx_ring_drv.free_ring)) {
        cancel_signal(state.rx_ring_drv.free_ring);
        microkit_notify_delayed(DRIVER_CH);
    }
}