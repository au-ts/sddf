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
    uint64_t rx_free;
    uint64_t rx_active;
    uint64_t queue_capacity;
    uint8_t client_id;
    uint64_t mac_addr;
};

struct resources {
    uint64_t rx_free_drv;
    uint64_t rx_active_drv;
    uint64_t drv_queue_capacity;
    uint64_t buffer_data_vaddr;
    uint64_t buffer_data_paddr;
    uint8_t driver_id;
    uint8_t num_network_clients;
    struct client clients[MAX_CLIENTS];
};

struct resources resources;

void sddf_notified(unsigned int ch);
void sddf_init();

#ifdef MICROKIT

/* Notification channels */
#define DRIVER_CH 0
#define CLIENT_0_CH 1
#define CLIENT_1_CH 2

/* Queue regions */
net_queue_t *rx_free_drv;
net_queue_t *rx_active_drv;
net_queue_t *rx_free_cli0;
net_queue_t *rx_active_cli0;

/* Buffer data regions */
uintptr_t buffer_data_vaddr;
uintptr_t buffer_data_paddr;

void init() {
    net_queue_info_t client_queue_info[MAX_CLIENTS] = {0};
    net_virt_queue_info(microkit_name, rx_free_cli0, rx_active_cli0, client_queue_info);

    uint64_t mac_addrs[MAX_CLIENTS] = {0};
    net_virt_mac_addrs(microkit_name, mac_addrs);

    resources = (struct resources) {
        .rx_free_drv = rx_free_drv,
        .rx_active_drv = rx_active_drv,
        .drv_queue_capacity = NET_RX_QUEUE_CAPACITY_DRIV,
        .buffer_data_vaddr = buffer_data_vaddr,
        .buffer_data_paddr = buffer_data_paddr,
        .driver_id = DRIVER_CH,
        .num_network_clients = NUM_NETWORK_CLIENTS,
        .clients = {},
    };

    for (int i = 0; i < NUM_NETWORK_CLIENTS; i++) {
        resources.clients[i] = (struct client) {
            .rx_free = client_queue_info[i].free,
            .rx_active = client_queue_info[i].active,
            .queue_capacity = client_queue_info[i].capacity,
            .client_id = CLIENT_0_CH + i,
            .mac_addr = mac_addrs[i]
        };
    }

    sddf_init();
}

#else

// TODO: THIS IS BAD, but what is the max size/can we implement the virt_rx differently?
#define NET_RX_QUEUE_CAPACITY_DRIV                   512

#endif /* MICROKIT */