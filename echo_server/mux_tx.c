#include "shared_ringbuffer.h"
#include "util.h"

uintptr_t tx_free_drv;
uintptr_t tx_used_drv;

uintptr_t tx_free_cli;
uintptr_t tx_used_cli;

uintptr_t shared_dma_vaddr_cli;
uintptr_t shared_dma_paddr_cli;
uintptr_t uart_base;

#define CLIENT_CH 0
#define NUM_CLIENTS 1
#define DRIVER_CH 1
#define DMA_SIZE 0x200000

typedef struct state {
    /* Pointers to shared buffers */
    ring_handle_t tx_ring_drv;
    ring_handle_t tx_ring_clients[NUM_CLIENTS];
} state_t;

state_t state;

static uintptr_t
get_phys_addr(uintptr_t virtual)
{
    uint64_t offset;
    if (virtual >= shared_dma_vaddr_cli && virtual < shared_dma_vaddr_cli + DMA_SIZE) {
        offset = virtual - shared_dma_vaddr_cli;
        if (offset < 0) {
            print("get_phys_addr: offset < 0");
            return 0;
        }
        return shared_dma_paddr_cli + offset;
    }
    print("get_phys_addr: virtual address not in range\n");
    return 0;
}

static uintptr_t
get_virt_addr(uintptr_t phys)
{
    uint64_t offset = -1;
    uintptr_t base = -1; 
    if (phys >= shared_dma_paddr_cli && phys < shared_dma_paddr_cli + DMA_SIZE) {
        offset = phys - shared_dma_paddr_cli;
        base = shared_dma_vaddr_cli;
    }

    if (offset < 0 || offset >= DMA_SIZE) {
        print("get_virt_addr: offset < 0");
        return 0;
    }

    return base + offset;
}

static int
get_client(uintptr_t addr)
{
    if (addr >= shared_dma_vaddr_cli && addr < shared_dma_vaddr_cli + DMA_SIZE) {
        return CLIENT_CH;
    }

    print("MUX TX|ERROR: Buffer out of range\n");
    assert(0);
    return 0;
}

/*
Loop over all used tx buffers in client queues and enqueue to driver.
TODO: Put client prioritisation in here.
*/
void process_tx_ready(void)
{
    uint64_t original_size = ring_size(state.tx_ring_drv.used_ring);
    uint64_t enqueued = 0;

    for (int client = 0; client < NUM_CLIENTS; client++) {
        while (!ring_empty(state.tx_ring_clients[client].used_ring) && !ring_full(state.tx_ring_drv.used_ring)) {
            uintptr_t addr;
            unsigned int len;
            void *cookie;

            int err = dequeue_used(&state.tx_ring_clients[client], &addr, &len, &cookie);
            assert(!err);
            uintptr_t phys = get_phys_addr(addr);
            assert(phys);
            err = enqueue_used(&state.tx_ring_drv, phys, len, cookie);
            assert(!err);

            enqueued += 1;
        }
    }

    if ((original_size == 0 || original_size + enqueued != ring_size(state.tx_ring_drv.used_ring)) && enqueued != 0) {
        sel4cp_notify_delayed(DRIVER_CH);
    }
}

/*
 * Take as many TX free buffers from the driver and give them to
 * the client. This will notify the client if we have moved buffers
 * around and the client's TX free ring was already empty.
 */
// TODO: Use the address range to determine which client
// this buffer originated from to return it to the correct one. 
void process_tx_complete(void)
{
    bool was_empty = ring_empty(state.tx_ring_clients[0].free_ring);
    bool enqueued = false;
    while (!ring_empty(state.tx_ring_drv.free_ring) && !ring_full(state.tx_ring_clients[0].free_ring)) {
        uintptr_t addr;
        unsigned int len;
        void *cookie;
        int err = dequeue_free(&state.tx_ring_drv, &addr, &len, &cookie);
        assert(!err);
        uintptr_t virt = get_virt_addr(addr);
        assert(virt);

        err = enqueue_free(&state.tx_ring_clients[get_client(virt)], virt, len, cookie);
        assert(!err);
        enqueued = true;
    }

    if (enqueued && was_empty) {
        sel4cp_notify(CLIENT_CH);
    }
}

void notified(sel4cp_channel ch)
{
    if (ch == CLIENT_CH || ch == DRIVER_CH) {
        process_tx_complete();
        process_tx_ready();
    } else {
       print("MUX TX|ERROR: unexpected notification from channel: ");
       puthex64(ch);
       print("\n");
       assert(0);
    }
}

void init(void)
{
    /* Set up shared memory regions */
    // FIX ME: Use the notify function pointer to put the notification in?
    ring_init(&state.tx_ring_drv, (ring_buffer_t *)tx_free_drv, (ring_buffer_t *)tx_used_drv, NULL, 1);
    ring_init(&state.tx_ring_clients[0], (ring_buffer_t *)tx_free_cli, (ring_buffer_t *)tx_used_cli, NULL, 0);

    print("MUX: initialised\n");

    return;
}
