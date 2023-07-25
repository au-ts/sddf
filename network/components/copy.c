#include "shared_ringbuffer.h"
#include "util.h"
#include <string.h>
#include <stdbool.h>

uintptr_t rx_free_mux;
uintptr_t rx_used_mux;

uintptr_t rx_free_cli;
uintptr_t rx_used_cli;

uintptr_t shared_dma_vaddr_mux;
uintptr_t shared_dma_vaddr_cli;
uintptr_t uart_base;

#define MUX_RX_CH 0
#define CLIENT_CH 1

#define BUF_SIZE 2048
#define NUM_BUFFERS 512
#define SHARED_DMA_SIZE (BUF_SIZE * NUM_BUFFERS)

ring_handle_t rx_ring_mux;
ring_handle_t rx_ring_cli;

void process_rx_complete(void)
{
    uint64_t enqueued = 0;
    // We only want to copy buffers if all the dequeues and enqueues will be successful
    while (!ring_empty(rx_ring_mux.used_ring) &&
            !ring_empty(rx_ring_cli.free_ring) &&
            !ring_full(rx_ring_mux.free_ring) &&
            !ring_full(rx_ring_cli.used_ring)) {

        uintptr_t m_addr, c_addr = 0;
        unsigned int m_len, c_len = 0;
        void *cookie = NULL;
        void *cookie2 = NULL;
        int err;

        err = dequeue_used(&rx_ring_mux, &m_addr, &m_len, &cookie);
        assert(!err);
        // get a free one from clients queue.
        err = dequeue_free(&rx_ring_cli, &c_addr, &c_len, &cookie2);
        assert(!err);
        if (!c_addr ||
                c_addr < shared_dma_vaddr_cli ||
                c_addr >= shared_dma_vaddr_cli + SHARED_DMA_SIZE)
        {
            print("COPY|ERROR: Received an insane address: ");
            puthex64(c_addr);
            print(". Address should be between ");
            puthex64(shared_dma_vaddr_cli);
            print(" and ");
            puthex64(shared_dma_vaddr_cli + SHARED_DMA_SIZE);
            print("\n");
        }

        if (c_len < m_len) {
            print("COPY|ERROR: client buffer length is less than mux buffer length.\n");
            print("client length: ");
            puthex64(c_len);
            print(" mux length: ");
            puthex64(m_len);
            print("\n");
        }
        // copy the data over to the clients address space.
        memcpy((void *)c_addr, (void *)m_addr, m_len);

        /* Now that we've copied the data, enqueue the buffer to the client's used ring. */
        err = enqueue_used(&rx_ring_cli, c_addr, m_len, cookie2);
        assert(!err);
        /* enqueue the old buffer back to dev_rx_ring.free so the driver can use it again. */
        err = enqueue_free(&rx_ring_mux, m_addr, BUF_SIZE, cookie);
        assert(!err);

        enqueued += 1;
    }

    if (rx_ring_cli.used_ring->notify_reader && enqueued) {
        sel4cp_notify_delayed(CLIENT_CH);
    }

    /* We want to inform the mux that more free buffers are available or the 
        used ring can now be refilled */
    if (enqueued && (rx_ring_mux.free_ring->notify_reader || rx_ring_mux.used_ring->notify_writer)) {
        if (have_signal && signal == BASE_OUTPUT_NOTIFICATION_CAP + CLIENT_CH) {
            // We need to notify the client, but this should
            // happen first. 
            sel4cp_notify(CLIENT_CH);
        }

        sel4cp_notify_delayed(MUX_RX_CH);
    }

    if (!ring_empty(rx_ring_mux.used_ring) || rx_ring_mux.free_ring->notify_reader) {
        // we want to be notified when this changes so we can continue
        // enqueuing packets to the client.
        rx_ring_cli.free_ring->notify_reader = true;
        // we don't need a notification from the multiplexer now. 
        // rx_ring_mux.used_ring->notify_reader = false;
    } else {
        rx_ring_cli.free_ring->notify_reader = false;
        // rx_ring_mux.used_ring->notify_reader = true;
    }
}

void notified(sel4cp_channel ch)
{
    if (ch == CLIENT_CH || ch == MUX_RX_CH) {
        /* We have one job. */
        process_rx_complete();
    } else {
        print("COPY|ERROR: unexpected notification from channel: ");
        puthex64(ch);
        print("\n");
        assert(0);
    }
}

void init(void)
{
    /* Set up shared memory regions */
    ring_init(&rx_ring_mux, (ring_buffer_t *)rx_free_mux, (ring_buffer_t *)rx_used_mux, 0, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&rx_ring_cli, (ring_buffer_t *)rx_free_cli, (ring_buffer_t *)rx_used_cli, 0, NUM_BUFFERS, NUM_BUFFERS);
    // ensure we get notified when a packet comes in 
    rx_ring_mux.used_ring->notify_reader = true;
    return;
}
