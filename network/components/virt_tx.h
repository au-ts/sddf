#pragma once
#ifdef MICROKIT
#include <sys/microkit.h>
#include <ethernet_config.h>
#else
#include <sys/extern.h>
#endif /* MICROKIT */
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

#ifdef MICROKIT
/* Microkit specific stuff */
#define DRIVER_CH 0
#define CLIENT_0_CH 1
#define CLIENT_1_CH 2

net_queue_t *tx_free_drv;
net_queue_t *tx_active_drv;
net_queue_t *tx_free_cli0;
net_queue_t *tx_active_cli0;
net_queue_t *tx_free_cli1;
net_queue_t *tx_active_cli1;

uintptr_t buffer_data_region_cli0_vaddr;
uintptr_t buffer_data_region_cli0_paddr;
uintptr_t buffer_data_region_cli1_vaddr;
uintptr_t buffer_data_region_cli1_paddr;

void init() {
    resources = (struct resources) {
        .tx_free_drv = tx_free_drv,
        .tx_active_drv = tx_active_drv,
        .drv_queue_size = NET_TX_QUEUE_SIZE_DRIV,
        .drv_id = DRIVER_CH,
        .clients = {},
    };

    resources.clients[0] = (struct client) {
        .tx_free = tx_free_cli0,
        .tx_active = tx_active_cli0,
        .queue_size = NET_TX_QUEUE_SIZE_CLI0,
        .buffer_data_region_vaddr = buffer_data_region_cli0_vaddr,
        .buffer_data_region_paddr = buffer_data_region_cli0_paddr,
        .client_id = CLIENT_0_CH,
    };

    // resources.clients[1] = (struct client) {
    //     .tx_free = tx_free_cli1,
    //     .tx_active = tx_active_cli1,
    //     .queue_size = NET_TX_QUEUE_SIZE_CLI1
    //     .buffer_data_region_vaddr = buffer_data_region_cli1_vaddr,
    //     .buffer_data_region_paddr = buffer_data_region_cli1_paddr,
    //     .client_ch = CLIENT_1_CH,
    //     .client_cap = BASE_OUTPUT_NOTIFICATION_CAP + CLIENT_1_CH,
    // };

    sddf_init();
}
#else
/* @alwin: Actually these should kinda be defined in rust and exported or something */
#define NUM_NETWORK_CLIENTS 1

#endif