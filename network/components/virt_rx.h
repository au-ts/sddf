#pragma once

#include <sel4/sel4.h>
#include <stdint.h>

#define MAX_CLIENTS 64

struct client {
    uint64_t rx_free;
    uint64_t rx_active;
    uint64_t queue_size;
    uint8_t client_id;
    uint64_t mac_addr;
};

struct resources {
    uint64_t rx_free_drv;
    uint64_t rx_active_drv;
    uint64_t drv_queue_size;
    uint64_t buffer_data_vaddr;
    uint64_t buffer_data_paddr;
    uint8_t driver_id;
    struct client clients[MAX_CLIENTS];
};

struct resources resources;

void sddf_notified(unsigned int ch);
void sddf_init();