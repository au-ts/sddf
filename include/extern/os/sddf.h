/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <sel4/sel4.h>
#include <stdint.h>

typedef unsigned int sddf_channel;

#define SDDF_NAME_LENGTH 64

extern char *sddf_get_pd_name();
extern void sddf_irq_ack(sddf_channel id);
extern void sddf_notify(sddf_channel id);
extern void sddf_deferred_notify(sddf_channel id);
extern void sddf_deferred_irq_ack(sddf_channel id);
extern seL4_MessageInfo_t sddf_ppcall(sddf_channel id, seL4_MessageInfo_t msginfo);
extern uint64_t sddf_get_mr(sddf_channel n);
extern void sddf_set_mr(sddf_channel n, uint64_t val);
extern sddf_channel sddf_deferred_notify_curr();
