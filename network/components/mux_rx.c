#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <microkit.h>
#include <sddf/network/shared_ringbuffer.h>
#include <sddf/network/constants.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

/* Notification channels */
#define DRIVER_CH 0
#define CLIENT_CH 1

/* Ring buffer regions */
uintptr_t rx_free_drv = 0x2000000;
uintptr_t rx_used_drv = 0x2200000;
uintptr_t rx_free_arp = 0x2400000;
uintptr_t rx_used_arp = 0x2600000;
uintptr_t rx_free_cli0 = 0x2800000;
uintptr_t rx_used_cli0 = 0x2a00000;
uintptr_t rx_free_cli1 = 0x2c00000;
uintptr_t rx_used_cli1 = 0x2e00000;

/* Buffer data regions */
uintptr_t buffer_data_vaddr = 0x3000000;
uintptr_t buffer_data_paddr = 0x11000000;

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

int rx_return(void)
{
    int i = 0;
    bool reprocess = true;
    bool notify_clients[NUM_CLIENTS] = {false};
    while (reprocess) {
        while (!ring_empty(state.rx_ring_drv.used_ring)) {
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_used(&state.rx_ring_drv, &buffer);
            assert(!err);

            buffer.phys_or_offset = buffer.phys_or_offset - buffer_data_paddr;
            // err = seL4_ARM_VSpace_Invalidate_Data(VSPACE_CAP, buffer.phys_or_offset + buffer_data_vaddr, buffer.phys_or_offset + buffer_data_vaddr + buffer.len);
            // if (err) dprintf("MUX_RX|ERROR: ARM Vspace invalidate failed\n");
            // assert(!err);

            int client = get_client((struct ethernet_header *) (buffer.phys_or_offset + buffer_data_vaddr));
            if (client >= 0) {
                err = enqueue_used(&state.rx_ring_clients[client], buffer);
                assert(!err);
                notify_clients[client] = true;
                // printf("%d", client);
            } else {
                buffer.phys_or_offset = buffer.phys_or_offset + buffer_data_paddr;
                err = enqueue_free(&state.rx_ring_drv, buffer);
                assert(!err);
                notify_drv = true;
                // printf("_");
            }
            if (i++ % 50 == 0) {
                // printf("\n");
            }
            i++;
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
            // microkit_notify(client + CLIENT_CH);
        }
    }

    return i;
}

int rx_provide(void)
{
    int i = 0;
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
                i++;
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
        // microkit_notify(DRIVER_CH);
    }

    return i;
}

void notified(microkit_channel ch)
{
}

void init(void)
{
    mux_mac_addr_init_sys("mux_rx", (uint8_t *) state.mac_addrs);

    ring_init(&state.rx_ring_drv, (ring_buffer_t *)rx_free_drv, (ring_buffer_t *)rx_used_drv, RX_RING_SIZE_DRIV);
    mux_ring_init_sys("mux_rx", state.rx_ring_clients, rx_free_arp, rx_used_arp);
    buffers_init((ring_buffer_t *)rx_free_drv, buffer_data_paddr, RX_RING_SIZE_DRIV);

    if (require_signal(state.rx_ring_drv.free_ring)) {
        cancel_signal(state.rx_ring_drv.free_ring);
        // microkit_notify(DRIVER_CH);
    }

    double useful = 0, redundant = 0;
    for (uint64_t i = 0; ; i++) {
        if (i % 100000000 == 0) {
            printf("mux_rx: %f%%\n", 100.0 * useful / (useful + redundant));
            useful = redundant = 0.0;
        }
        int j = rx_return();
        j += rx_provide();
        if (j != 0) {
            useful += 1.0;
        } else {
            redundant += 1.0;
        }
    }
}
