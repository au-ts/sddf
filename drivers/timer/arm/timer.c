/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/util/udivmodti4.h>
#include <sddf/resources/device.h>

#if !(CONFIG_EXPORT_PCNT_USER && CONFIG_EXPORT_PTMR_USER)
#error "ARM generic timer is not exported by seL4"
#endif

static uint64_t timer_freq;

#define MAX_TIMEOUTS 6

#define GENERIC_TIMER_ENABLE (1 << 0)
#define GENERIC_TIMER_IMASK  (1 << 1)
#define GENERIC_TIMER_STATUS (1 << 2)
#define LOW_WORD(x) (x & 0xffffffffffffffff)
#define HIGH_WORD(x) (x >> 64)

#define COPROC_WRITE_WORD(R,W) asm volatile ("msr " R  ", %0" :: "r"(W))
#define COPROC_READ_WORD(R,W)  asm volatile ("mrs %0, " R : "=r" (W))
#define COPROC_WRITE_64(R,W)   COPROC_WRITE_WORD(R,W)
#define COPROC_READ_64(R,W)    COPROC_READ_WORD(R,W)

/* control reigster for the el1 physical timer */
#define CNTP_CTL "cntp_ctl_el0"
/* holds the compare value for the el1 physical timer */
#define CNTP_CVAL "cntp_cval_el0"
/* holds the 64-bit physical count value */
#define CNTPCT "cntpct_el0"
/* frequency of the timer */
#define CNTFRQ "cntfrq_el0"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

static inline uint64_t get_ticks(void)
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

static inline void generic_timer_enable(void)
{
    generic_timer_or_ctrl(GENERIC_TIMER_ENABLE);
}

static inline void generic_timer_disable(void)
{
    generic_timer_or_ctrl(~GENERIC_TIMER_ENABLE);
}

#define KHZ (1000)
#define MHZ (1000 * KHZ)
#define GHZ (1000 * MHZ)

static inline uint64_t freq_cycles_and_hz_to_ns(uint64_t ncycles, uint64_t hz)
{
    if (hz % GHZ == 0) {
        return ncycles / (hz / GHZ);
    } else if (hz % MHZ == 0) {
        return ncycles * MS_IN_S / (hz / MHZ);
    } else if (hz % KHZ == 0) {
        return ncycles * US_IN_S / (hz / KHZ);
    }

    __uint128_t ncycles_in_s = (__uint128_t)ncycles * NS_IN_S;
    /* We can discard the remainder. */
    uint64_t rem = 0;
    uint64_t res = udiv128by64to64(HIGH_WORD(ncycles_in_s), LOW_WORD(ncycles_in_s), NS_IN_S, &rem);

    return res;
}

static inline uint64_t freq_ns_and_hz_to_cycles(uint64_t ns, uint64_t hz)
{
    __uint128_t calc = ((__uint128_t)ns * (__uint128_t)hz);
    /* We can discard the remainder. */
    uint64_t rem = 0;
    uint64_t res = udiv128by64to64(HIGH_WORD(calc), LOW_WORD(calc), NS_IN_S, &rem);

    return res;
}

void set_timeout(uint64_t timeout)
{
    generic_timer_set_compare(freq_ns_and_hz_to_cycles(timeout, timer_freq));
}

static uint64_t timeouts[MAX_TIMEOUTS];

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            sddf_notify(i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
            next_timeout = timeouts[i];
        }
    }

    if (next_timeout != UINT64_MAX) {
        set_timeout(next_timeout);
    }

}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 0);

    /* Ack any IRQs that were delivered before the driver started. */
    sddf_irq_ack(device_resources.irqs[0].id);

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    generic_timer_set_compare(UINT64_MAX);
    generic_timer_enable();
    timer_freq = generic_timer_get_freq();
}

void notified(sddf_channel ch)
{
    assert(ch == device_resources.irqs[0].id);
    sddf_deferred_irq_ack(ch);

    generic_timer_set_compare(UINT64_MAX);
    uint64_t curr_time = freq_cycles_and_hz_to_ns(get_ticks(), timer_freq);
    process_timeouts(curr_time);
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    switch (seL4_MessageInfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = freq_cycles_and_hz_to_ns(get_ticks(), timer_freq);
        sddf_set_mr(0, time_ns);
        return seL4_MessageInfo_new(0, 0, 0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = freq_cycles_and_hz_to_ns(get_ticks(), timer_freq);
        uint64_t offset_us = (uint64_t)(sddf_get_mr(0));
        timeouts[ch] = curr_time + offset_us;
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n",
                     seL4_MessageInfo_get_label(msginfo), ch);
        break;
    }

    return seL4_MessageInfo_new(0, 0, 0, 0);
}
