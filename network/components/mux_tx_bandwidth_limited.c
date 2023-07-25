#include "shared_ringbuffer.h"
#include "util.h"
#include <math.h>

uintptr_t tx_free_drv;
uintptr_t tx_used_drv;
uintptr_t tx_free_cli0;
uintptr_t tx_used_cli0;
uintptr_t tx_free_cli1;
uintptr_t tx_used_cli1;
uintptr_t tx_free_arp;
uintptr_t tx_used_arp;

uintptr_t shared_dma_vaddr_cli0;
uintptr_t shared_dma_paddr_cli0;
uintptr_t shared_dma_vaddr_cli1;
uintptr_t shared_dma_paddr_cli1;
uintptr_t shared_dma_vaddr_arp;
uintptr_t shared_dma_paddr_arp;
uintptr_t uart_base;

#define CLIENT_0 0
#define CLIENT_1 1
#define ARP 2
#define NUM_CLIENTS 3
#define TIMER_CH 4
#define DRIVER 3
#define NUM_BUFFERS 512
#define BUF_SIZE 2048
#define DMA_SIZE 0x200000

#define TIME_WINDOW 10000ULL // 10 milliseconds

#define GET_TIME 0
#define SET_TIMEOUT 1

typedef struct client_usage {
    uint64_t last_time;
    uint64_t curr_bandwidth;
    uint64_t max_bandwidth;
    bool pending_timeout;
} client_usage_t;

typedef struct state {
    /* Pointers to shared buffers */
    ring_handle_t tx_ring_drv;
    ring_handle_t tx_ring_clients[NUM_CLIENTS];
    client_usage_t client_usage[NUM_CLIENTS];
} state_t;

state_t state;

static uintptr_t
get_phys_addr(uintptr_t virtual)
{
    int offset;
    uintptr_t base;
    if (virtual >= shared_dma_vaddr_cli0 && virtual < shared_dma_vaddr_cli0 + DMA_SIZE) {
        offset = virtual - shared_dma_vaddr_cli0;
        base = shared_dma_paddr_cli0;
    } else if (virtual >= shared_dma_vaddr_cli1 && virtual < shared_dma_vaddr_cli1 + DMA_SIZE) {
        offset = virtual - shared_dma_vaddr_cli1;
        base = shared_dma_paddr_cli1;
    } else if (virtual >= shared_dma_vaddr_arp && virtual < shared_dma_vaddr_arp + DMA_SIZE) {
        offset = virtual - shared_dma_vaddr_arp;
        base = shared_dma_paddr_arp;
    } else {
        print("MUX TX|ERROR: get_phys_addr: invalid virtual address\n");
        return 0;
    }

    return base + offset;
}

static uintptr_t
get_virt_addr(uintptr_t phys)
{
    int offset;
    uintptr_t base; 
    if (phys >= shared_dma_paddr_cli0 && phys < shared_dma_paddr_cli0 + DMA_SIZE) {
        offset = phys - shared_dma_paddr_cli0;
        base = shared_dma_vaddr_cli0;
    } else if (phys >= shared_dma_paddr_cli1 && phys < shared_dma_paddr_cli1 + DMA_SIZE) {
        offset = phys - shared_dma_paddr_cli1;
        base = shared_dma_vaddr_cli1;
    }else if (phys >= shared_dma_paddr_arp && phys < shared_dma_paddr_arp + DMA_SIZE) {
        offset = phys - shared_dma_paddr_arp;
        base = shared_dma_vaddr_arp;
    } else {
        print("MUX TX|ERROR: get_virt_addr: invalid physical address\n");
        return 0;
    }

    return base + offset;
}

static int
get_client(uintptr_t addr)
{
    int client;
    if (addr >= shared_dma_vaddr_cli0 && addr < shared_dma_vaddr_cli0 + DMA_SIZE) {
        client = CLIENT_0;
    } else if (addr >= shared_dma_vaddr_cli1 && addr < shared_dma_vaddr_cli1 + DMA_SIZE) {
        client = CLIENT_1;
    } else if (addr >= shared_dma_vaddr_arp && addr < shared_dma_vaddr_arp + DMA_SIZE) {
        client = ARP;
    } else {
        print("MUX TX|ERROR: Buffer out of range\n");
        assert(0);
    }

    return client;
}

// TODO: Map the timer into this address space with RDONLY so we can get the curr_time more efficiently...  
static uint64_t
get_time(void)
{
    sel4cp_ppcall(TIMER_CH, sel4cp_msginfo_new(GET_TIME, 0));
    uint64_t time_now = seL4_GetMR(0);
    return time_now;
}

static void
set_timeout(uint64_t timeout)
{
    sel4cp_mr_set(0, timeout);
    sel4cp_ppcall(TIMER_CH, sel4cp_msginfo_new(SET_TIMEOUT, 1));
}

void process_tx_ready(void)
{
    uint64_t enqueued = 0;
    bool driver_ntfn = false;
    int err;
    uint64_t curr_time = get_time();

    for (int client = 0; client < NUM_CLIENTS; client++) {
        // Was the last time we serviced this client inside the time window? 
        if (curr_time - state.client_usage[client].last_time >= TIME_WINDOW) {
            state.client_usage[client].curr_bandwidth = 0;
            state.client_usage[client].last_time = curr_time;
        }

        while (!ring_empty(state.tx_ring_clients[client].used_ring) && !ring_full(state.tx_ring_drv.used_ring)
                && (state.client_usage[client].curr_bandwidth < state.client_usage[client].max_bandwidth)) {
            uintptr_t addr;
            unsigned int len;
            void *cookie;
            uintptr_t phys;

            err = dequeue_used(&state.tx_ring_clients[client], &addr, &len, &cookie);
            assert(!err);
            phys = get_phys_addr(addr);
            assert(phys);
            err = enqueue_used(&state.tx_ring_drv, phys, len, cookie);
            assert(!err);

            enqueued += 1;
            state.client_usage[client].curr_bandwidth += (len * 8);
        }

        if (state.tx_ring_clients[client].free_ring->notify_reader) {
            /* If any of the clients are requesting a notification, 
                then ensure the driver notifies mux when transmit is finished
                so it can notify the client. */
            driver_ntfn = true;
        }

        if (!ring_empty(state.tx_ring_clients[client].used_ring) && !state.client_usage[client].pending_timeout) {
            // request a time out. so we come back to this client. 
            // THOUGHT: how will the timer inform us which clients queue to look at? 
            set_timeout(TIME_WINDOW - (curr_time - state.client_usage[client].last_time));
            state.client_usage[client].pending_timeout = true;
            state.tx_ring_clients[client].used_ring->notify_reader = false;
        }
    }

    if (state.tx_ring_drv.used_ring->notify_reader && enqueued) {
        sel4cp_notify_delayed(DRIVER);
    }

    /* Ensure we get a notification when transmit is complete
      so we can dequeue free buffers and return them to the client. */
    state.tx_ring_drv.free_ring->notify_reader = driver_ntfn;
}

/*
 * Take as many TX free buffers from the driver and give them to
 * the respective clients. This will notify the clients if we have moved buffers
 * around and the client's TX free ring was empty.
 */
void process_tx_complete(void)
{
    // bitmap stores whether which clients need notifying.
    bool notify_clients[NUM_CLIENTS] = {false};
    bool driver_ntfn = false;

    while (!ring_empty(state.tx_ring_drv.free_ring)) {
        uintptr_t addr;
        unsigned int len;
        void *cookie;
        int err = dequeue_free(&state.tx_ring_drv, &addr, &len, &cookie);
        assert(!err);
        uintptr_t virt = get_virt_addr(addr);
        assert(virt);

        int client = get_client(virt);
        err = enqueue_free(&state.tx_ring_clients[client], virt, len, cookie);
        assert(!err);

        if (state.tx_ring_clients[client].free_ring->notify_reader) {
            notify_clients[client] = true;
            /* If any of the clients are requesting a notification, 
                then ensure the driver notifies tx mux so we can notify 
                the client. */
            driver_ntfn = true;
        }
    }

    /* Loop over bitmap and see who we need to notify. */
    for (int client = 0; client < NUM_CLIENTS; client++) {
        if (notify_clients[client]) {
            sel4cp_notify(client);
        }
    }
    state.tx_ring_drv.free_ring->notify_reader = driver_ntfn;
}

void notified(sel4cp_channel ch)
{
    if (ch == TIMER_CH) {
        /* TODO: 
         * Currently the timer driver only supports one timeout per client at a time. 
         * as this mux only limits client 1, this is a bit of a hack. 
         * in future we need to manage this properly. */ 
        state.client_usage[1].pending_timeout = false;
        state.tx_ring_clients[1].used_ring->notify_reader = true;
    }
    process_tx_complete();
    process_tx_ready();
}

void init(void)
{
    /* Set up shared memory regions */
    // FIX ME: Use the notify function pointer to put the notification in?
    ring_init(&state.tx_ring_drv, (ring_buffer_t *)tx_free_drv, (ring_buffer_t *)tx_used_drv, 1, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&state.tx_ring_clients[0], (ring_buffer_t *)tx_free_cli0, (ring_buffer_t *)tx_used_cli0, 1, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&state.tx_ring_clients[1], (ring_buffer_t *)tx_free_cli1, (ring_buffer_t *)tx_used_cli1, 1, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&state.tx_ring_clients[2], (ring_buffer_t *)tx_free_arp, (ring_buffer_t *)tx_used_arp, 1, NUM_BUFFERS, NUM_BUFFERS);

    /* Enqueue free transmit buffers to all clients. */
    int err;
    uintptr_t addr;

    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        addr = shared_dma_vaddr_cli0 + (BUF_SIZE * i);
        err = enqueue_free(&state.tx_ring_clients[0], addr, BUF_SIZE, NULL);
        assert(!err);
    }

    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        addr = shared_dma_vaddr_cli1 + (BUF_SIZE * i);
        err = enqueue_free(&state.tx_ring_clients[1], addr, BUF_SIZE, NULL);
        assert(!err);
    }

    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        addr = shared_dma_vaddr_arp + (BUF_SIZE * i);
        err = enqueue_free(&state.tx_ring_clients[2], addr, BUF_SIZE, NULL);
        assert(!err);
    }

    // We are higher priority than the clients, so we always need to be notified
    // when a used buffer becomes available to be sent. 
    state.tx_ring_clients[0].used_ring->notify_reader = true;
    state.tx_ring_clients[1].used_ring->notify_reader = true;
    state.tx_ring_clients[2].used_ring->notify_reader = true;

    state.client_usage[0].last_time = 0;//
    state.client_usage[0].max_bandwidth = 100000000; // theoretically no limit
    state.client_usage[0].curr_bandwidth = 0;
    state.client_usage[0].pending_timeout = false;
    state.client_usage[1].last_time = 0;//
    state.client_usage[1].max_bandwidth = 1000000; // 100Mbps for the TIME_WINDOW
    state.client_usage[1].curr_bandwidth = 0;
    state.client_usage[1].pending_timeout = false;
    state.client_usage[2].last_time = 0;//
    state.client_usage[2].max_bandwidth = 100000000;
    state.client_usage[2].curr_bandwidth = 0;
    state.client_usage[2].pending_timeout = false;

    return;
}
