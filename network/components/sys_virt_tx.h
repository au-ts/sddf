#pragma once
#include "virt_tx.h"

#ifdef MICROKIT
#include <microkit.h>
#include <ethernet_config.h>

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


inline void sddf_notify_delayed(microkit_channel ch) {
    microkit_notify_delayed(ch);
}

inline void sddf_notify(microkit_channel ch) {
	microkit_notify(ch);
}


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

void notified(microkit_channel ch) {
	sddf_notified(ch);
}

#else
#include <sel4/sel4.h>

extern void sddf_notify_delayed(unsigned int id);
extern void sddf_notify(unsigned int id);

/* @alwin: Actually these should kinda be defined in rust and exported or something */
#define NET_TX_QUEUE_SIZE_DRIV 512
#define NUM_NETWORK_CLIENTS 1

#endif /* MICROKIT */
