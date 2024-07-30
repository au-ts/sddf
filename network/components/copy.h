#pragma once

// #include <sel4/sel4.h>
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