#pragma once

#include "virt_rx.h"

#ifdef MICROKIT
#include <ethernet_config.h>

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

inline void sddf_notify_delayed(microkit_channel ch) {
    microkit_notify_delayed(ch);
}

inline void sddf_notify(microkit_channel ch) {
	microkit_notify(ch);
}

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

void notified(microkit_channel ch) {
	sddf_notified(ch);
}

#else

#define NET_RX_QUEUE_SIZE_DRIV 512
#define NET_RX_QUEUE_SIZE_DRIV 512
#define NUM_NETWORK_CLIENTS 1

extern void sddf_notify_delayed(unsigned int id);
extern void sddf_notify(unsigned int id);

#endif /* MICROKIT */


