#pragma once

#include <sel4/sel4.h>
#include <stdint.h>

extern void sddf_irq_ack(unsigned int id);
extern void sddf_notify(unsigned int id);
extern void sddf_notify_delayed(unsigned int id);
extern seL4_MessageInfo_t sddf_ppcall(unsigned int id, seL4_MessageInfo_t msginfo);
extern uint64_t sddf_get_mr(unsigned int n);
extern void sddf_set_mr(unsigned int n, uint64_t val);
inline unsigned int sddf_notify_delayed_curr();