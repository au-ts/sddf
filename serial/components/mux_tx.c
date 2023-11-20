/* The policy of the mux tx is that all clients can always request to transmit */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sel4/sel4.h>
#include "shared_ringbuffer.h"
#include "util/include/util.h"
#include "uart.h"

/* TODO: ADD IN DIFFERENT COLOURS TO DIFFERENTIATE DIFFERENT CLIENT STREAMS */

#define DRIVER_CH 9

#ifndef NUM_CLIENTS
#error "NUM_CLIENTS is expected to be defined for TX serial multiplexor"
#endif

#define COLOUR_START_LEN 5
#define COLOUR_END_LEN 4

char *client_colours[] = { "\x1b[31m", "\x1b[32m" };
char *client_colour_end = "\x1b[0m";

/* Memory regions as defined in the system file */

// Transmit rings with the driver
uintptr_t tx_free_driver;
uintptr_t tx_used_driver;

// Transmit rings with the client
uintptr_t tx_free_client;
uintptr_t tx_used_client;
uintptr_t tx_free_client2;
uintptr_t tx_used_client2;

uintptr_t tx_data_driver;
uintptr_t tx_data_client;
uintptr_t tx_data_client2;

// Have an array of client rings.
ring_handle_t tx_ring[NUM_CLIENTS];
ring_handle_t drv_tx_ring;

int handle_tx(int curr_client) {
    // Copy data from the client ring to the driver rings.
    uintptr_t buffer = 0;
    unsigned int buffer_len = 0;
    void *cookie = 0;

    bool was_empty = ring_empty(drv_tx_ring.used_ring);

    // Loop over all clients here
    for (int client = 0; client < NUM_CLIENTS; client++) {
        // The client can plug their ring. If plugged, we won't process it.
        if (ring_plugged(tx_ring[client].used_ring)) {
            continue;
        }
        while (!dequeue_used(&tx_ring[client], &buffer, &buffer_len, &cookie)) {
            // We want to enqueue into the drivers used ring
            uintptr_t drv_buffer = 0;
            unsigned int drv_len = 0;
            void *drv_cookie = 0;

            int ret = driver_dequeue(drv_tx_ring.free_ring, &drv_buffer, &drv_len, &drv_cookie);
            if (ret != 0) {
                microkit_dbg_puts("Failed to dequeue buffer from drv tx avail ring\n");
                return 1;
            }

            assert(buffer_len + COLOUR_START_LEN + COLOUR_START_LEN <= BUFFER_SIZE);
            /* First copy the colour start bytes */
            size_t len_copied = 0;
            memcpy((char *) drv_buffer, client_colours[client], COLOUR_START_LEN);
            len_copied += COLOUR_START_LEN;
            /* Then the actual colour */
            uintptr_t dest_buffer = drv_buffer + COLOUR_START_LEN;
            char *string = (char *) buffer;
            memcpy((char *) dest_buffer, string, buffer_len);
            len_copied += buffer_len;
            /* And then finally the colour end bytes */
            memcpy((char *)(dest_buffer + buffer_len), client_colour_end, COLOUR_END_LEN);
            len_copied += COLOUR_END_LEN;

            drv_cookie = cookie;

            ret = enqueue_used(&drv_tx_ring, drv_buffer, len_copied, drv_cookie);
            if (ret != 0) {
                microkit_dbg_puts("Failed to enqueue buffer to drv tx used ring\n");
                // Don't know if I should return here, because we need to enqueue a
                // serpeate buffer
            }

            // enqueue back to the client free ring
            enqueue_free(&tx_ring[client], buffer, BUFFER_SIZE, cookie);
        }
    }

    if (was_empty) {
        microkit_notify(DRIVER_CH);
    }

    return 0;
}

void init (void) {
    // We want to init the client rings here. Currently this only inits one client
    ring_init(&tx_ring[0], (ring_buffer_t *)tx_free_client, (ring_buffer_t *)tx_used_client, 0, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&tx_ring[1], (ring_buffer_t *)tx_free_client2, (ring_buffer_t *)tx_used_client2, 0, NUM_BUFFERS, NUM_BUFFERS);
    ring_init(&drv_tx_ring, (ring_buffer_t *)tx_free_driver, (ring_buffer_t *)tx_used_driver, 0, NUM_BUFFERS, NUM_BUFFERS);

    // Add buffers to the drv tx ring from our shared dma region
    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        // Have to start at the memory region left of by the rx ring
        int ret = enqueue_free(&drv_tx_ring, tx_data_driver + ((i + NUM_BUFFERS) * BUFFER_SIZE), BUFFER_SIZE, NULL);

        if (ret != 0) {
            microkit_dbg_puts(microkit_name);
            microkit_dbg_puts(": tx buffer population, unable to enqueue buffer\n");
        }
    }
}

void notified(microkit_channel ch) {
    // We should only ever recieve notifications from the client
    // Sanity check the client
    if (ch < 1 || ch > NUM_CLIENTS) {
        microkit_dbg_puts("Received a bad client channel\n");
        return;
    }

    handle_tx(ch);
}
