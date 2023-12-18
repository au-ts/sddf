#pragma once

#include <sddf/serial/shared_ringbuffer.h>

struct serial_server {
    /* Pointers to shared_ringbuffers */
    ring_handle_t rx_ring;
    ring_handle_t tx_ring;
};

#define SERVER_PRINT_CHANNEL 9
#define SERVER_GETCHAR_CHANNEL 11

// These are also defined in the uart.h header file
#define NUM_BUFFERS 512
#define BUFFER_SIZE 2048
