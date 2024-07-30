#pragma once

#include "copy.h"

#ifdef MICROKIT
#include <ethernet_config.h>

#define VIRT_RX_CH 0
#define CLIENT_CH 1

net_queue_t *rx_free_virt;
net_queue_t *rx_active_virt;
net_queue_t *rx_free_cli;
net_queue_t *rx_active_cli;

uintptr_t virt_buffer_data_region;
uintptr_t cli_buffer_data_region;

void init() {
	resources = (struct resources) {
		.virt_free = rx_free_virt,
		.virt_active = rx_active_virt,
		.cli_free = rx_free_cli,
		.cli_active = rx_active_cli,
		.virt_data = virt_buffer_data_region,
		.cli_data = cli_buffer_data_region

		.virt_id = VIRT_RX_CH,
		.cli_id = CLIENT_CH
	}

	sddf_init()
}

#else

extern void sddf_notify(unsigned int ch);
extern void sddf_notify_delayed(unsigned int ch);


#endif /* MICROKIT */