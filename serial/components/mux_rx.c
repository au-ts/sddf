/* MUX is currently limited to a max of 9 clients */
#include <stdbool.h>
#include <stdint.h>
#include <sel4cp.h>
#include <sel4/sel4.h>
#include <string.h>
#include "shared_ringbuffer.h"
#include "util.h"
#include "uart.h"

#define CLI_CH 1
#define DRV_CH 11

#define NUM_CLIENTS 2

/* Memory regions as defined in the system file */

// Transmit rings with the driver
uintptr_t rx_free_drv;
uintptr_t rx_used_drv;

// Transmit rings with the client
uintptr_t rx_free_cli;
uintptr_t rx_used_cli;
uintptr_t rx_free_cli2;
uintptr_t rx_used_cli2;

uintptr_t shared_dma_rx_drv;
uintptr_t shared_dma_rx_cli;
uintptr_t shared_dma_rx_cli2;

// Have an array of client rings. 
ring_handle_t rx_ring[NUM_CLIENTS];
ring_handle_t drv_rx_ring;

/* We need to do some processing of the input stream to determine when we need 
to change direction. */

/* To switch input direction, type the "@" symbol followed immediately by a number.
Otherwise, can put "\" before "@" to escape this.*/

int mux_state;
int client;
// We want to keep track of each clients requests, so that they can be serviced once we have changed 
// input direction
int num_to_get_chars[NUM_CLIENTS];
int multi_client;

int give_multi_char(char got_char) {
    for (int curr_client = 0; curr_client < NUM_CLIENTS; curr_client++) {

        if (num_to_get_chars[curr_client] <= 0) {
            return 1;
        }
        // Address that we will pass to dequeue to store the buffer address
        uintptr_t buffer = 0;
        // Integer to store the length of the buffer
        unsigned int buffer_len = 0; 

        void *cookie = 0;

        int ret = dequeue_free(&rx_ring[curr_client], &buffer, &buffer_len, &cookie);

        if (ret != 0) {
            sel4cp_dbg_puts(sel4cp_name);
            sel4cp_dbg_puts(": unable to dequeue from the rx free ring\n");
            return;
        }

        ((char *) buffer)[0] = (char) got_char;

        // Now place in the rx used ring
        ret = enqueue_used(&rx_ring[curr_client], buffer, 1, &cookie);

        if (ret != 0) {
            sel4cp_dbg_puts(sel4cp_name);
            sel4cp_dbg_puts(": unable to enqueue to the tx free ring\n");
            return 1;
        }

        num_to_get_chars[curr_client] -= 1;
    }
}

int give_single_char(int curr_client, char got_char) {
    if (curr_client < 1 || curr_client > NUM_CLIENTS) {
        return 1;
    }

    if (num_to_get_chars[curr_client - 1] <= 0) {
        return 1;
    }
    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0; 

    void *cookie = 0;

    int ret = dequeue_free(&rx_ring[curr_client - 1], &buffer, &buffer_len, &cookie);

    if (ret != 0) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": unable to dequeue from the rx free ring\n");
        return;
    }

    ((char *) buffer)[0] = (char) got_char;

    // Now place in the rx used ring
    ret = enqueue_used(&rx_ring[curr_client - 1], buffer, 1, &cookie);

    if (ret != 0) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": unable to enqueue to the tx free ring\n");
        return 1;
    }

    num_to_get_chars[curr_client - 1] -= 1;
}

int give_char(int curr_client, char got_char) {
    if (multi_client == 1) {
        give_multi_char(got_char);
    } else {
        give_single_char(curr_client, got_char);
    }
}


/* We will check for escape characters in here, as well as dealing with switching direction*/
void handle_rx() {
    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0; 

    void *cookie = 0;

    // We can only be here if we have been notified by the driver
    int ret = dequeue_used(&drv_rx_ring, &buffer, &buffer_len, &cookie) != 0;
    if (ret != 0) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": getchar - unable to dequeue used buffer\n");
    }

    // We are only getting one character at a time, so we just need to cast the buffer to an int

    char got_char = *((char *) buffer);

    /* Now that we are finished with the used buffer, we can add it back to the free ring*/

    ret = enqueue_free(&drv_rx_ring, buffer, buffer_len, NULL);

    if (ret != 0) {
        sel4cp_dbg_puts(sel4cp_name);
        sel4cp_dbg_puts(": getchar - unable to enqueue used buffer back into free ring\n");
    }

    // We have now gotten a character, deal with the input direction switch
    if (mux_state == 1) {
        // The previous character was an escape character
        give_char(client, got_char);
        mux_state = 0;
    }  else if (mux_state == 2) {
        // We are now switching input direction

        // Case for simultaneous multi client input
        if (got_char == 'm') {
            multi_client = 1;
            client = -1;
        } else {
            // Ensure that multi client input is off
            multi_client = 0;
            int new_client = atoi(&got_char);
            // We also want this to show in the terminal, so print it
            // print(&got_char);
            if (new_client < 1 || new_client > NUM_CLIENTS) {
                sel4cp_dbg_puts("Attempted to switch to invalid client number\n");
            } else {
                client = new_client;
            }
        }

        mux_state = 0;
    } else if (mux_state == 0) {
        // No escape character has been set
        if (got_char == '\\') {
            mux_state = 1;
            // The next character is going to be escaped
        } else if (got_char == '@') {
            mux_state = 2;
        } else {
            give_char(client, got_char);
        }
    }
}

void init (void) {
    // We want to init the client rings here. Currently this only inits one client
    ring_init(&rx_ring[0], (ring_buffer_t *)rx_free_cli, (ring_buffer_t *)rx_used_cli, 0, 512, 512);
    ring_init(&rx_ring[1], (ring_buffer_t *)rx_free_cli2, (ring_buffer_t *)rx_used_cli2, 0, 512, 512);

    ring_init(&drv_rx_ring, (ring_buffer_t *)rx_free_drv, (ring_buffer_t *)rx_used_drv, 0, 512, 512);

    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        int ret = enqueue_free(&drv_rx_ring, shared_dma_rx_drv + (i * BUFFER_SIZE), BUFFER_SIZE, NULL);

        if (ret != 0) {
            sel4cp_dbg_puts(sel4cp_name);
            sel4cp_dbg_puts(": mux rx buffer population, unable to enqueue buffer\n");
            return;
        }
    }

    // We initialise the current client to 1
    client = 1;
    // Set the current escape character to 0, we can't have recieved an escape character yet
    mux_state = 0;
    // Disable simultaneous multi client input
    multi_client = 0;
    // No chars have been requested yet
    num_to_get_chars[0] = 0;
    num_to_get_chars[1] = 0;
}

void notified(sel4cp_channel ch) {
    // We should only ever recieve notifications from the client
    // Sanity check the client
    if (ch == DRV_CH) {
        handle_rx();
    } else if (ch < 1 || ch > NUM_CLIENTS) {
        sel4cp_dbg_puts("Received a bad client channel\n");
        return;
    }  else {
        // This was recieved on a client channel. Index the number of characters to get
        num_to_get_chars[ch - 1] += 1;
    }
}