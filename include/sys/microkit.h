#pragma once

#include <microkit.h>
#include <sel4/sel4.h>

void notified(microkit_channel ch) {
	sddf_notified(ch);
}

static inline void sddf_irq_ack(microkit_channel ch) {
	microkit_irq_ack(ch);
}

void sddf_irq_ack_delayed(microkit_channel ch) {
	sddf_irq_ack_delayed(ch);
}

static inline void sddf_notify(microkit_channel ch) {
	microkit_notify(ch);
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

inline microkit_msginfo sddf_ppcall(microkit_channel ch, microkit_msginfo msginfo) {
	microkit_ppcall(ch, msginfo);
}

inline uint64_t sddf_get_mr(unsigned int n) {
	return seL4_GetMR(n);
}

inline void sddf_set_mr(unsigned int n, uint64_t val) {
	seL4_SetMR(n, val);
}
