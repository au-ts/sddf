#pragma once

#include "timer.h"

#ifdef MICROKIT
#include <microkit.h>

/* The current code is kinda weird for dealing with client channels */

#define IRQ_CH 0

void init() {
	resources = (struct resources) {
		.irq_id = IRQ_CH,
	}

	sddf_init();
}

void sddf_irq_ack_delayed(microkit_channel ch) {
	sddf_irq_ack_delayed(ch);
}

#else
#include <sel4/sel4.h>

extern void sddf_notify(unsigned int id);
extern void sddf_irq_ack_delayed(unsigned int id);
extern seL4_MessageInfo_t sddf_ppcall(unsigned int id, seL4_MessageInfo_t msginfo);
extern uint64_t sddf_get_mr(unsigned int n);
extern void sddf_set_mr(unsigned int n, uint64_t val);

#endif /* MICROKIT */
