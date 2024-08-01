#pragma once

#include "lwip.h"

#ifdef MICROKIT
#include <microkit.h>
#include <serial_config.h>
#include <ethernet_config.h>

#define SERIAL_TX_CH 0
#define TIMER  1
#define RX_CH  2
#define TX_CH  3

net_queue_t *rx_free;
net_queue_t *rx_active;
net_queue_t *tx_free;
net_queue_t *tx_active;
uintptr_t rx_buffer_data_region;
uintptr_t tx_buffer_data_region;

void init() {
    resources = (struct resources) {
    	.rx_free = rx_free,
    	.rx_active = rx_active,
   		.rx_queue_size = NET_RX_QUEUE_SIZE_CLI0,
    	.tx_free = tx_free,
    	.tx_active = tx_active,
   		.tx_queue_size = NET_TX_QUEUE_SIZE_CLI0,

    	.rx_buffer_data_region = rx_buffer_data_region,
    	.tx_buffer_data_region = tx_buffer_data_region,

        .timer_id = TIMER,
        .rx_id = RX_CH,
        .tx_id = TX_CH,
    };

    sddf_init();
}

void notified(microkit_channel ch) {
	sddf_notified(ch);
}

inline void sddf_notify_delayed(microkit_channel ch) {
	microkit_notify_delayed(ch);
}

inline unsigned int sddf_notify_delayed_curr() {
	if (!have_signal) {
		return -1;
	}

	return signal_cap - BASE_OUTPUT_NOTIFICATION_CAP;
}

inline void sddf_notify(microkit_channel ch) {
	microkit_notify(ch);
}

inline microkit_msginfo sddf_ppcall(microkit_channel ch, microkit_msginfo msginfo) {
	microkit_ppcall(ch, msginfo);
}

#else


#define NET_MAX_CLIENT_QUEUE_SIZE 512
#define NET_RX_QUEUE_SIZE_CLI0 512
#define NET_TX_QUEUE_SIZE_CLI0 512
#define MAC_ADDR_CLI0                       0x525401000001

extern void sddf_notify_delayed(unsigned int id);
extern void sddf_notify(unsigned int id);
extern unsigned int sddf_notify_delayed_curr();
extern seL4_MessageInfo_t sddf_ppcall(unsigned int id, seL4_MessageInfo_t msginfo);
extern uint64_t sddf_get_mr(unsigned int n);
extern void sddf_set_mr(unsigned int n, uint64_t val);

#endif /* MICROKIT */

