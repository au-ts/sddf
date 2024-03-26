#include <microkit.h>

#include <sddf/network/shared_ringbuffer.h>
#include <sddf/util/cache.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define DRIVER 0
#define CLIENT_CH 1

uintptr_t tx_free_drv = 0x2000000;
uintptr_t tx_used_drv = 0x2200000;

uintptr_t tx_free_arp = 0x2400000;
uintptr_t tx_used_arp = 0x2600000;
uintptr_t tx_free_cli0 = 0x2800000;
uintptr_t tx_used_cli0 = 0x2a00000;
uintptr_t tx_free_cli1 = 0x2c00000;
uintptr_t tx_used_cli1 = 0x2e00000;

uintptr_t buffer_data_region_arp_vaddr = 0x3000000;
uintptr_t buffer_data_region_cli0_vaddr = 0x3200000;
uintptr_t buffer_data_region_cli1_vaddr = 0x3400000;

uintptr_t buffer_data_region_arp_paddr = 0x11200000;
uintptr_t buffer_data_region_cli0_paddr = 0x11400000;
uintptr_t buffer_data_region_cli1_paddr = 0x11600000;

typedef struct state {
    ring_handle_t tx_ring_drv;
    ring_handle_t tx_ring_clients[NUM_CLIENTS];
    uintptr_t buffer_region_vaddrs[NUM_CLIENTS];
    uintptr_t buffer_region_paddrs[NUM_CLIENTS];
} state_t;

state_t state;

int extract_offset(uintptr_t *phys) {
    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (*phys >= state.buffer_region_paddrs[client] && 
            *phys < state.buffer_region_paddrs[client] + state.tx_ring_clients[client].free_ring->size * BUFF_SIZE) {
            *phys = *phys - state.buffer_region_paddrs[client];
            return client;
        }
    }
    return -1;
}

void tx_provide(void)
{
    bool enqueued = false;
    for (int client = 0; client < NUM_CLIENTS; client++) {
        bool reprocess = true;
        while (reprocess) {
            while (!ring_empty(state.tx_ring_clients[client].used_ring)) {
                buff_desc_t buffer;
                int err __attribute__((unused)) = dequeue_used(&state.tx_ring_clients[client], &buffer);
                assert(!err);

                if (buffer.phys_or_offset % BUFF_SIZE || 
                    buffer.phys_or_offset >= BUFF_SIZE * state.tx_ring_clients[client].used_ring->size) {
                    dprintf("MUX_TX|LOG: Client provided offset %llx which is not buffer aligned or outside of buffer region\n", buffer.phys_or_offset);
                    err = enqueue_free(&state.tx_ring_clients[client], buffer);
                    assert(!err);
                    continue;
                }

                cache_clean(buffer.phys_or_offset + state.buffer_region_vaddrs[client], buffer.phys_or_offset + state.buffer_region_vaddrs[client] + buffer.len);

                buffer.phys_or_offset = buffer.phys_or_offset + state.buffer_region_paddrs[client];
                err = enqueue_used(&state.tx_ring_drv, buffer);
                assert(!err);
                enqueued = true;
            }

            request_signal(state.tx_ring_clients[client].used_ring);
            reprocess = false;

            if (!ring_empty(state.tx_ring_clients[client].used_ring)) {
                cancel_signal(state.tx_ring_clients[client].used_ring);
                reprocess = true;
            }
        }
    }

    if (enqueued && require_signal(state.tx_ring_drv.used_ring)) {
        cancel_signal(state.tx_ring_drv.used_ring);
        microkit_notify_delayed(DRIVER);
    }
}

void tx_return(void)
{
    bool reprocess = true;
    bool notify_clients[NUM_CLIENTS] = {false};
    while (reprocess) {
        while (!ring_empty(state.tx_ring_drv.free_ring)) {
            buff_desc_t buffer;
            int err __attribute__((unused)) = dequeue_free(&state.tx_ring_drv, &buffer);
            assert(!err);

            int client = extract_offset(&buffer.phys_or_offset);
            assert(client >= 0);

            err = enqueue_free(&state.tx_ring_clients[client], buffer);
            assert(!err);
            notify_clients[client] = true;
        }

        request_signal(state.tx_ring_drv.free_ring);
        reprocess = false;

        if (!ring_empty(state.tx_ring_drv.free_ring)) {
            cancel_signal(state.tx_ring_drv.free_ring);
            reprocess = true;
        }
    }

    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (notify_clients[client] && require_signal(state.tx_ring_clients[client].free_ring)) {
            cancel_signal(state.tx_ring_clients[client].free_ring);
            microkit_notify(client + CLIENT_CH);
        }
    }
}

void notified(microkit_channel ch)
{
    tx_return();
    tx_provide();
}

void init(void)
{
    ring_init(&state.tx_ring_drv, (ring_buffer_t *)tx_free_drv, (ring_buffer_t *)tx_used_drv, TX_RING_SIZE_DRIV);

    mux_ring_init_sys("mux_tx", state.tx_ring_clients, tx_free_arp, tx_used_arp);
    
    mem_region_init_sys("mux_tx", state.buffer_region_vaddrs, buffer_data_region_arp_vaddr);

    /* CDTODO: Can we make this system agnostic? */
    state.buffer_region_paddrs[0] = buffer_data_region_arp_paddr;
    state.buffer_region_paddrs[1] = buffer_data_region_cli0_paddr;
    state.buffer_region_paddrs[2] = buffer_data_region_cli1_paddr;
    
    tx_provide();
}
