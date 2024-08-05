#pragma once

#ifdef MICROKIT
#include <sys/microkit.h>
#include <serial_config.h>
#include <ethernet_config.h>
#else
#include <sys/extern.h>
#endif /* MICROKIT */
#include <sel4/sel4.h>
#include <stdint.h>

struct resources {
	uint64_t rx_free;
	uint64_t rx_active;
	uint64_t rx_queue_size;
	uint64_t tx_free;
	uint64_t tx_active;
	uint64_t tx_queue_size;
	uint64_t rx_buffer_data_region;
	uint64_t tx_buffer_data_region;
	uint64_t mac_addr;

	uint8_t timer_id;
	uint8_t rx_id;
	uint8_t tx_id;
};

struct resources resources;

void sddf_init(void);
void sddf_notified(unsigned int id);

#ifdef MICROKIT
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
	size_t rx_queue_size, tx_queue_size;
	net_cli_queue_info(microkit_name, &rx_queue_size, &tx_queue_size);
	uint64_t mac_addr = net_cli_mac_addr_info(microkit_name);

    resources = (struct resources) {
    	.rx_free = rx_free,
    	.rx_active = rx_active,
   		.rx_queue_size = rx_queue_size,
    	.tx_free = tx_free,
    	.tx_active = tx_active,
   		.tx_queue_size = tx_queue_size,

    	.rx_buffer_data_region = rx_buffer_data_region,
    	.tx_buffer_data_region = tx_buffer_data_region,
    	.mac_addr = mac_addr,

        .timer_id = TIMER,
        .rx_id = RX_CH,
        .tx_id = TX_CH,
    };

    sddf_init();
}

#else

#define NET_MAX_CLIENT_QUEUE_SIZE 512 //@alwin: What to do about this?

#endif /* MICROKIT */
