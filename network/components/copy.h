#pragma once

#ifdef MICROKIT
#include <sys/microkit.h>
#include <ethernet_config.h>
#else
#include <sys/extern.h>
#endif /* MICROKIT */
#include <sel4/sel4.h>
#include <stdint.h>

struct resources {
	uint64_t virt_free;
	uint64_t virt_active;
	uint64_t virt_queue_size;
	uint64_t cli_free;
	uint64_t cli_active;
	uint64_t cli_queue_size;
	uint64_t virt_data;
	uint64_t cli_data;

	uint8_t virt_id;
	uint8_t cli_id
};

struct resources resources;

void sddf_notified(unsigned int ch);
void sddf_init();

#ifdef MICROKIT

#define VIRT_RX_CH 0
#define CLIENT_CH 1

net_queue_t *rx_free_virt;
net_queue_t *rx_active_virt;
net_queue_t *rx_free_cli;
net_queue_t *rx_active_cli;

uintptr_t virt_buffer_data_region;
uintptr_t cli_buffer_data_region;

void init() {
	size_t cli_queue_size, virt_queue_size;

	net_copy_queue_info(microkit_name, &cli_queue_size, &virt_queue_size);

	resources = (struct resources) {
		.virt_free = rx_free_virt,
		.virt_active = rx_active_virt,
		.virt_queue_size = cli_queue_size,
		.cli_free = rx_free_cli,
		.cli_active = rx_active_cli,
		.cli_queue_size = virt_queue_size,
		.virt_data = virt_buffer_data_region,
		.cli_data = cli_buffer_data_region,

		.virt_id = VIRT_RX_CH,
		.cli_id = CLIENT_CH
	};

	sddf_init();
}

#else

#endif /* MICROKIT */