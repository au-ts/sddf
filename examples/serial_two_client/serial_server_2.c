#include <microkit.h>
#include "serial_server.h"
#include <sddf/serial/util.h>

/* Queue handle components -
Need to have access to the same queue mechanisms as the driver, so that we can enqueue
buffers to be serviced by the driver.*/

uintptr_t rx_free;
uintptr_t rx_active;
uintptr_t tx_free;
uintptr_t tx_active;

uintptr_t rx_data;
uintptr_t tx_data;

struct serial_server global_serial_server = {0};

/*
Return -1 on failure.
*/
int serial_server_printf(char *string) {
    struct serial_server *local_server = &global_serial_server;

    // Get a buffer from the tx queue

    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;
    // Integer to store the length of the buffer
    unsigned int buffer_len = 0;
    void *cookie = 0;

    // Dequeue a buffer from the free queue from the tx buffer
    int ret = serial_dequeue_free(&local_server->tx_queue, &buffer, &buffer_len, &cookie);

    if(ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": serial server printf, unable to dequeue from tx queue, tx queue empty\n");
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

    // We then need to add this buffer to the transmit active queue structure

    bool is_empty = serial_queue_empty(local_server->tx_queue.active);

    ret = serial_enqueue_active(&local_server->tx_queue, buffer, print_len, cookie);

    if(ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": serial server printf, unable to enqueue to tx active queue\n");
        return -1;
    }

    /*
    First we will check if the transmit active queue is empty. If not empty, then the driver was processing
    the active queue, however it was not finished, potentially running out of budget and being pre-empted. 
    Therefore, we can just add the buffer to the active queue, and wait for the driver to resume. However if 
    empty, then we can notify the driver to start processing the active queue.
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

    /* Now that we have notified the driver, we can attempt to dequeue from the active queue.
    When the driver has processed an interrupt, it will add the inputted character to the active queue.*/
    
    // Address that we will pass to dequeue to store the buffer address
    uintptr_t buffer = 0;

    // Integer to store the length of the buffer
    unsigned int buffer_len = 0; 

    void *cookie = 0;

    while (serial_dequeue_active(&local_server->rx_queue, &buffer, &buffer_len, &cookie) != 0) {
        /* The queue is currently empty, as there is no character to get. 
        We will spin here until we have gotten a character. As the driver is a higher priority than us, 
        it should be able to pre-empt this loop
        */
        microkit_dbg_puts(""); /* From Patrick, this is apparently needed to stop the compiler from optimising out the 
        as it is currently empty. When compiled in a release version the puts statement will be compiled
        into a nop command.
        */
    }

    // We are only getting one character at a time, so we just need to cast the buffer to an int
    char got_char = *((char *) buffer);

    /* Now that we are finished with the active buffer, we can add it back to the free queue*/
    int ret = serial_enqueue_free(&local_server->rx_queue, buffer, buffer_len, NULL);

    if (ret != 0) {
        microkit_dbg_puts(microkit_name);
        microkit_dbg_puts(": getchar - unable to enqueue active buffer back into available queue\n");
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

    // Here we need to init queue buffers and other data structures

    struct serial_server *local_server = &global_serial_server;
    
    // Init the shared queue buffers
    serial_queue_init(&local_server->rx_queue, (serial_queue_t *)rx_free, (serial_queue_t *)rx_active, 0, 512, 512);
    // We will also need to populate these queues with memory from the shared dma region
    
    // Add buffers to the rx queue
    for (int i = 0; i < NUM_ENTRIES - 1; i++) {
        int ret = serial_enqueue_free(&local_server->rx_queue, rx_data + (i * BUFFER_SIZE), BUFFER_SIZE, NULL);

        if (ret != 0) {
            microkit_dbg_puts(microkit_name);
            microkit_dbg_puts(": server rx buffer population, unable to enqueue buffer\n");
        }
    }

    serial_queue_init(&local_server->tx_queue, (serial_queue_t *)tx_free, (serial_queue_t *)tx_active, 0, 512, 512);

    // Add buffers to the tx queue
    for (int i = 0; i < NUM_ENTRIES - 1; i++) {
        // Have to start at the memory region left of by the rx queue
        int ret = serial_enqueue_free(&local_server->tx_queue, tx_data + ((i + NUM_ENTRIES) * BUFFER_SIZE), BUFFER_SIZE, NULL);

        if (ret != 0) {
            microkit_dbg_puts(microkit_name);
            microkit_dbg_puts(": server tx buffer population, unable to enqueue buffer\n");
        }
    }

    // Plug the tx active queue
    serial_queue_plug(local_server->tx_queue.active);

    /* Some basic tests for the serial driver */

    serial_server_printf("Attempting to use the server printf! -- FROM SERVER 2\n");

    // Unplug the tx active queue
    serial_queue_unplug(local_server->tx_queue.active);
    microkit_notify(SERVER_PRINT_CHANNEL);

    serial_server_printf("Enter char to test getchar FOR SERIAL 2\n");
    char test = getchar();
    serial_server_printf("We got the following char in SERIAL 2: ");
    serial_server_printf(&test);
    serial_server_printf("\n");
    serial_server_printf("Enter char to test getchar -- SERIAL 2\n");
    test = getchar();
    serial_server_printf("We got the following char in SERIAL 2: ");
    serial_server_printf(&test);

    serial_server_printf("\nEnter char to test scanf IN SERIAL 2\n");

    char temp_buffer = 0;

    int scanf_ret = serial_server_scanf(&temp_buffer);

    if (scanf_ret == -1) {
        serial_server_printf("Issue with scanf\n");
    } else {
        serial_server_printf(&temp_buffer);
    }

    serial_server_printf("\n---END OF SERIAL 2 TEST---\n");
    
}


void notified(microkit_channel ch) {
    return;
}