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

#define MAX_CLIENTS 64

void init() {
    queue_info_t client_queue_info[MAX_CLIENTS];
    net_virt_queue_info(microkit_name, tx_free_cli0, tx_active_cli0, client_queue_info);

    uintptr_t buffer_region_vaddrs[MAX_CLIENTS];
    net_mem_region_info(microkit_name, buffer_region_vaddrs, buffer_data_region_cli0_vaddr);

    resources = (struct resources) {
        .tx_free_drv = tx_free_drv,
        .tx_active_drv = tx_active_drv,
        .drv_queue_size = NET_TX_QUEUE_SIZE_DRIV,
        .drv_id = DRIVER_CH,
        .clients = {},
    };

    for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
        resources.clients[i] = (struct client) {
            .tx_free = client_queue_info[i].free,
            .tx_active =  client_queue_info[i].active,
            .queue_size = client_queue_info[i].size,
            .buffer_data_region_vaddr = buffer_region_vaddrs[i],
            .client_id = CLIENT_0_CH + i,
        };
    }

    resources.clients[0].buffer_data_region_paddr = buffer_data_region_cli0_paddr;
    resources.clients[1].buffer_data_region_paddr = buffer_data_region_cli1_paddr;

    sddf_init();
}
#else
/* @alwin: Actually these should kinda be defined in rust and exported or something */
#define NUM_NETWORK_CLIENTS 1

#endif