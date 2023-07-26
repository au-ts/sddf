#pragma once
#include "shared_ringbuffer.h"

struct serial_server {
    /* Pointers to shared_ringbuffers */
    ring_handle_t rx_ring;
    ring_handle_t tx_ring;
};

#define SERVER_PRINT_CHANNEL 9
#define SERVER_GETCHAR_CHANNEL 11