#pragma once

#include <sel4/sel4.h>
#include <stdint.h>

#define MAX_TIMEOUTS 6

struct resources {
	uint8_t irq_id
};

struct resources resources;

void sddf_notified(unsigned int ch);
void sddf_init();
