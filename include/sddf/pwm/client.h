/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

// TODO: might want read-pwm calls
#define SDDF_PWM_PPC_ID_SET_NS          (1)

#define SDDF_PWM_PPC_SLOT_CHANNEL       (0)
#define SDDF_PWM_PPC_SLOT_PERIOD        (1)
#define SDDF_PWM_PPC_SLOT_PULSE_WIDTH   (2)
#define SDDF_PWM_PPC_SLOT_FLAGS         (3)

/* Flip polarity of output signal */
#define SDDF_PWM_FLAG_INVERT_POLARITY   BIT(0)

#define SDDF_PWM_SUCCESS (0)
#define SDDF_PWM_FAILURE (1)

static inline bool sddf_pwm_set_ns(microkit_channel ch, seL4_Word channel, seL4_Word period_ns, seL4_Word pulse_width_ns, seL4_Word flags)
{
    microkit_msginfo msginfo;

    msginfo = microkit_msginfo_new(SDDF_PWM_PPC_ID_SET_NS, 4);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_CHANNEL, channel);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_PERIOD, period_ns);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_PULSE_WIDTH, pulse_width_ns);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_FLAGS, flags);

    msginfo = sddf_ppcall(ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == SDDF_PWM_SUCCESS;
}

// duty cycle encoded as a [0, 100) value
static inline bool sddf_pwm_set_freq_duty(microkit_channel ch, seL4_Word channel, seL4_Word freq, seL4_Word duty_cycle, seL4_Word flags)
{
    microkit_msginfo msginfo;

    // TODO: safe division
    seL4_Word period_ns = 1000000000ULL / freq;
    seL4_Word pulse_width_ns = period_ns * duty_cycle / 1000;

    msginfo = microkit_msginfo_new(SDDF_PWM_PPC_ID_SET_NS, 4);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_CHANNEL, channel);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_PERIOD, period_ns);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_PULSE_WIDTH, pulse_width_ns);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_FLAGS, flags);

    msginfo = sddf_ppcall(ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == SDDF_PWM_SUCCESS;
}

static inline bool sddf_pwm_disable(microkit_channel ch, seL4_Word channel)
{
    microkit_msginfo msginfo;

    /* A PWM disable is encoded as a set with period = 0, pulse width = 0 */

    msginfo = microkit_msginfo_new(SDDF_PWM_PPC_ID_SET_NS, 4);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_CHANNEL, channel);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_PERIOD, 0x0);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_PULSE_WIDTH, 0x0);
    sddf_set_mr(SDDF_PWM_PPC_SLOT_FLAGS, 0x0);

    msginfo = sddf_ppcall(ch, msginfo);

    return microkit_msginfo_get_label(msginfo) == SDDF_PWM_SUCCESS;
}
