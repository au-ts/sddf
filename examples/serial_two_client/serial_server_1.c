#include <microkit.h>
#include "serial_server.h"
#include "shared_ringbuffer.h"
#include "serial/components/util.h"

/* Ring handle components -
Need to have access to the same ring buffer mechanisms as the driver, so that we can enqueue
buffers to be serviced by the driver.*/

uintptr_t rx_free;
uintptr_t rx_used;
uintptr_t tx_free;
uintptr_t tx_used;

uintptr_t rx_data;
uintptr_t tx_data;

struct serial_server global_serial_server = {0};

/*
Return -1 on failure.
*/
int serial_server_printf(char *string) {
    struct serial_server *local_server = &global_serial_server;
    // Get a buffer from the tx ring

    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0;
    void *cookie = 0;

    // Dequeue a buffer from the free ring from the tx buffer
    int ret = dequeue_free(&local_server->tx_ring, &buffer, &buffer_len, &cookie);

    if(ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": serial server printf, unable to dequeue from tx ring, tx ring empty\n");
        return -1;
    }

    // Need to copy over the string into the buffer, if it is less than the buffer length
    int print_len = strlen(string) + 1;

    if(print_len > BUFFER_SIZE) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": print string too long for buffer\n");
        return -1;
    }

    // Copy over the string to be printed to the buffer
    memcpy((char *) buffer, string, print_len);

    // We then need to add this buffer to the transmit used ring structure

    bool is_empty = ring_empty(local_server->tx_ring.used_ring);

    ret = enqueue_used(&local_server->tx_ring, buffer, print_len, cookie);

    if(ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": serial server printf, unable to enqueue to tx used ring\n");
        return -1;
    }

    /*
    First we will check if the transmit used ring is empty. If not empty, then the driver was processing
    the used ring, however it was not finished, potentially running out of budget and being pre-empted.
    Therefore, we can just add the buffer to the used ring, and wait for the driver to resume. However if
    empty, then we can notify the driver to start processing the used ring.
    */

    if(is_empty) {
        // Notify the driver through the printf channel
        microkit_notify(SERVER_PRINT_CHANNEL);
    }

    return 0;
}

// Return char on success, -1 on failure
int getchar() {
    // Notify the driver that we want to get a character. In Patrick's design, this increments
    // the chars_for_clients value.
    microkit_notify(SERVER_GETCHAR_CHANNEL);

    struct serial_server *local_server = &global_serial_server;

    /* Now that we have notified the driver, we can attempt to dequeue from the used ring.
    When the driver has processed an interrupt, it will add the inputted character to the used ring.*/

    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0; 

    void *cookie = 0;

    while (dequeue_used(&local_server->rx_ring, &buffer, &buffer_len, &cookie) != 0) {
        /* The ring is currently empty, as there is no character to get.
        We will spin here until we have gotten a character. As the driver is a higher priority than us,
        it should be able to pre-empt this loop
        */
        asm("nop");
    }

    // We are only getting one character at a time, so we just need to cast the buffer to an int

    char got_char = *((char *) buffer);

    /* Now that we are finished with the used buffer, we can add it back to the free ring*/

    int ret = enqueue_free(&local_server->rx_ring, buffer, buffer_len, NULL);

    if (ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": getchar - unable to enqueue used buffer back into free ring\n");
    }

    return (int) got_char;
}

/* Return 0 on success, -1 on failure.
Basic scanf implementation using the getchar function above. Gets characters until
CTRL+C or CTRL+D or new line.
NOT MEMORY SAFE
*/
int serial_server_scanf(char* buffer) {
    int i = 0;
    int getchar_ret = getchar();

    if (getchar_ret == -1) {
        microkit_dbg_puts("Error getting char\n");
        return -1;
    }


    while(getchar_ret != '\03' && getchar_ret != '\04' && getchar_ret != '\r') {
        ((char *) buffer)[i] = (char) getchar_ret;

        getchar_ret = getchar();

        if (getchar_ret == -1) {
            microkit_dbg_puts("Error getting char\n");
            return -1;
        }

        i++;
    }

    return 0;
}

// Init function required by sel4cp, initialise serial datastructres for server here
void init(void) {
    microkit_dbg_puts(microkit_name);
    microkit_dbg_puts(": elf PD init function running\n");

    // Here we need to init ring buffers and other data structures

    struct serial_server *local_server = &global_serial_server;

    // Init the shared ring buffers
    ring_init(&local_server->rx_ring, (ring_buffer_t *)rx_free, (ring_buffer_t *)rx_used, 0, 512, 512);
    // We will also need to populate these rings with memory from the shared dma region

    // Add buffers to the rx ring
    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        int ret = enqueue_free(&local_server->rx_ring, rx_data + (i * BUFFER_SIZE), BUFFER_SIZE, NULL);

        if (ret != 0) {
            microkit_dbg_puts(microkit_name);
            microkit_dbg_puts(": server rx buffer population, unable to enqueue buffer\n");
        }
    }

    ring_init(&local_server->tx_ring, (ring_buffer_t *)tx_free, (ring_buffer_t *)tx_used, 0, 512, 512);

    // Add buffers to the tx ring
    for (int i = 0; i < NUM_BUFFERS - 1; i++) {
        // Have to start at the memory region left of by the rx ring
        int ret = enqueue_free(&local_server->tx_ring, tx_data + ((i + NUM_BUFFERS) * BUFFER_SIZE), BUFFER_SIZE, NULL);

        if (ret != 0) {
            microkit_dbg_puts(microkit_name);
            microkit_dbg_puts(": server tx buffer population, unable to enqueue buffer\n");
        }
    }

    /* Some basic tests for the serial driver */

    ring_plug(local_server->tx_ring.used_ring);

    serial_server_printf("Attempting to use the server printf! -- FROM SERVER 1\n");

    serial_server_printf("Enter char to test getchar FOR SERIAL 1\n");
    ring_unplug(local_server->tx_ring.used_ring);
    microkit_notify(SERVER_PRINT_CHANNEL);

    char test = getchar();
    serial_server_printf("We got the following char in SERIAL 1: ");
    serial_server_printf(&test);
    serial_server_printf("\n");
    serial_server_printf("Enter char to test getchar -- SERIAL 1\n");
    test = getchar();
    serial_server_printf("We got the following char in SERIAL 1: ");
    serial_server_printf(&test);

    serial_server_printf("\nEnter char to test scanf IN SERIAL 1\n");

    char temp_buffer = 0;

    int scanf_ret = serial_server_scanf(&temp_buffer);

    if (scanf_ret == -1) {
        serial_server_printf("Issue with scanf\n");
    } else {
        serial_server_printf(&temp_buffer);
    }

    serial_server_printf("\n---END OF SERIAL 1 TEST---\n");
}

void notified(microkit_channel ch) {
    return;
}
