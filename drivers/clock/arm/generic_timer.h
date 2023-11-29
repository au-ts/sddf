/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include "coproc.h"
#include "timer.h"

#define BIT(nr) (1UL << (nr))

#define GENERIC_TIMER_ENABLE BIT(0)
#define GENERIC_TIMER_IMASK  BIT(1)
#define GENERIC_TIMER_STATUS BIT(2)
/* Tested to work on ARM A53's */
#define GENERIC_TIMER_PCNT_IRQ 30

/*
 * This timer will only work if the kernel has configured
 * CNTPCT to be read from user-level. This is done by setting CONFIG_EXPORT_PCNT_USER in
 * a kernel configuration.
 */
typedef struct {
    uint32_t freq;
} generic_timer_t;

static inline timer_properties_t get_generic_timer_properties(void)
{
    return (timer_properties_t) {
        .upcounter = true,
        .bit_width = 64
    };
}

static inline uint64_t generic_timer_get_ticks(void)
{
    uint64_t time;
    COPROC_READ_64(CNTPCT, time);
    return time;
}

static inline void generic_timer_set_compare(uint64_t ticks)
{
    COPROC_WRITE_64(CNTP_CVAL, ticks);
}

static inline uint32_t generic_timer_get_freq(void)
{
    uintptr_t freq;
    COPROC_READ_WORD(CNTFRQ, freq);
    return (uint32_t) freq;
}

static inline uint32_t generic_timer_read_ctrl(void)
{
    uintptr_t ctrl;
    COPROC_READ_WORD(CNTP_CTL, ctrl);
    return ctrl;
}

static inline void generic_timer_write_ctrl(uintptr_t ctrl)
{
    COPROC_WRITE_WORD(CNTP_CTL, ctrl);
}

static inline void generic_timer_or_ctrl(uintptr_t bits)
{
    uintptr_t ctrl = generic_timer_read_ctrl();
    generic_timer_write_ctrl(ctrl | bits);
}

static inline void generic_timer_and_ctrl(uintptr_t bits)
{
    uintptr_t ctrl = generic_timer_read_ctrl();
    generic_timer_write_ctrl(ctrl & bits);
}

static inline void generic_timer_enable(void)
{
    generic_timer_or_ctrl(GENERIC_TIMER_ENABLE);
}

static inline void generic_timer_disable(void)
{
    generic_timer_and_ctrl(~GENERIC_TIMER_ENABLE);
}

static inline void generic_timer_unmask_irq(void)
{
    generic_timer_and_ctrl(~GENERIC_TIMER_IMASK);
}

static inline void generic_timer_mask_irq(void)
{
    generic_timer_or_ctrl(GENERIC_TIMER_IMASK);
}

static inline uintptr_t generic_timer_status(void)
{
    return generic_timer_read_ctrl() & GENERIC_TIMER_STATUS;
}

int generic_timer_init(generic_timer_t *timer);
uint64_t generic_timer_get_time(generic_timer_t *timer);
