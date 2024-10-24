#pragma once

#include <microkit.h>
#include <sel4/sel4.h>
#include <stdint.h>

void sddf_init(void);
void sddf_notified(uint32_t ch);

void notified(microkit_channel ch) {
	sddf_notified(ch);
}

static inline void sddf_irq_ack(microkit_channel ch) {
	microkit_irq_ack(ch);
}

void sddf_deferred_irq_ack(microkit_channel ch) {
	microkit_deferred_irq_ack(ch);
}

static inline void sddf_notify(microkit_channel ch) {
	microkit_notify(ch);
}

inline void sddf_deferred_notify(microkit_channel ch) {
    microkit_deferred_notify(ch);
}

inline unsigned int sddf_deferred_notify_curr() {
	if (!microkit_have_signal) {
		return -1;
	}

	return microkit_signal_cap - BASE_OUTPUT_NOTIFICATION_CAP;
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
