#pragma once

#include <sel4/sel4.h>
#include <stdint.h>


#define MAX_CLIENTS 64

struct client {
    uint64_t tx_free;
    uint64_t tx_active;
    uint64_t queue_size;
    uint8_t client_id;
    uint64_t buffer_data_region_vaddr;
    uint64_t buffer_data_region_paddr;
};

struct resources {
    uint64_t tx_free_drv;
    uint64_t tx_active_drv;
    uint64_t drv_queue_size;
    uint8_t drv_id;
    struct client clients[MAX_CLIENTS];
};

struct resources resources;

void sddf_notified(unsigned int ch);
void sddf_init();