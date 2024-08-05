#pragma once

#ifdef MICROKIT
#include <sys/microkit.h>
#else
#include <sys/extern.h>
#endif /* MICROKIT */
#include <sel4/sel4.h>
#include <stdint.h>

#define MAX_TIMEOUTS 6

struct resources {
	uint8_t irq_id
};

struct resources resources;

void sddf_notified(unsigned int ch);
void sddf_init();

#ifdef MICROKIT

#define IRQ_CH 0

void init() {
	resources = (struct resources) {
		.irq_id = IRQ_CH,
	};

	sddf_init();
}

#endif /* MICROKIT */
