/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "pwm.h"

#include <os/sddf.h>
#include <sddf/util/printf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PWM DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PWM DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


#define CH_PWM_IRQ 0
#define CH_CONTROL_PPC 1


void init(void)
{
    LOG_DRIVER("PWM starting\n");
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("Unexpected notification on channel %u\n", ch);
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_DRIVER("ppc from channel %u\n", ch);

    switch (microkit_msginfo_get_label(msginfo)) {
    default:
        LOG_DRIVER("Unknown request %lu from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        // XXXX.
        return microkit_msginfo_new(0, 0);
    }
}
