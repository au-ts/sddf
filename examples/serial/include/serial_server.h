#pragma once

#include <sddf/serial/queue.h>

struct serial_server {
    /* Pointers to shared_ringbuffers */
    serial_queue_handle_t rx_queue;
    serial_queue_handle_t tx_queue;
};

#define SERVER_PRINT_CHANNEL 9
#define SERVER_GETCHAR_CHANNEL 11

// These are also defined in the uart.h header file
#define NUM_ENTRIES 512
#define BUFFER_SIZE 2048
