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
net_queue_t *rx_free_cli1;
net_queue_t *rx_active_cli1;

/* Buffer data regions */
uintptr_t buffer_data_vaddr;
uintptr_t buffer_data_paddr;

void init() {
        resources = (struct resources) {
        .rx_free_drv = rx_free_drv,
        .rx_active_drv = rx_active_drv,
        .drv_queue_size = NET_RX_QUEUE_SIZE_DRIV,
        .buffer_data_vaddr = buffer_data_vaddr,
        .buffer_data_paddr = buffer_data_paddr,
        .driver_id = DRIVER_CH,
        .clients = {},
    };

    resources.clients[0] = (struct client) {
        .rx_free = rx_free_cli0,
        .rx_active = rx_active_cli0,
        .queue_size = NET_RX_QUEUE_SIZE_COPY0,
        .client_id = CLIENT_0_CH,
        .mac_addr = MAC_ADDR_CLI0,
    };

    // resources.clients[1] = (struct client) {
    //     .rx_free = rx_free_cli1,
    //     .rx_active = rx_active_cli1,
    //     .queue_size = NET_RX_QUEUE_SIZE_COPY1,
    //     .client_ch = CLIENT_1_CH,
    //     .client_cap = BASE_OUTPUT_NOTIFICATION_CAP + CLIENT_1_CH,
    //     .mac_addr = MAC_ADDR_CLI1,
    // };

    sddf_init();
}

#else

#define NUM_NETWORK_CLIENTS 1
#define NET_RX_QUEUE_SIZE_DRIV 512 //@alwin: What to do about this?

#endif