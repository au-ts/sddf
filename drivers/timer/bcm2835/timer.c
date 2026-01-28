/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <sddf/resources/device.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

#if !defined(CONFIG_PLAT_BCM2711)
#error "Driver assumes 100MHz clock frequency, check if your platform supports that"
#endif

/*
 * The system timer has four 32-bit compare registers available.
 * Channels 0 and 2 are used by the VideoCore and cause spurious interrupts
 * (see: https://github.com/seL4/seL4/pull/894)
*/
#define BCM2835_TIMEOUT_TIMER 1

typedef struct {
    /* Registers
     * BCM2835 System Timer peripheral provides four 32-bit timer channels
     * and one 64-bit free running counter. */
    uint32_t cs;    /* 0x00: system timer control/status */
    uint32_t clo;   /* 0x04: system timer counter lower 32 bits */
    uint32_t chi;   /* 0x08: system timer counter higher 32 bits */
    uint32_t cn[4]; /* 0x0c - 0x18: system timer compare 0-3 */
} bcm2835_timer_regs_t;

static volatile bcm2835_timer_regs_t *timer_regs;

/*
 * The system timer status register has bits 31:4 reserved by default.
 * Bits 3:0 correspond to the compare registers c3:c0 respectively.
 * If a bit is set, it means that a match is detected between the free running counter
 * and the timeout time in the respective register. This is routed to the interrupt controller.
 *
 * The bits are of type W1C (write 1 to clear) so writing a 1 to the relevant bit clears the match
 * status bit and its corresponding interrupt line. Since we are only using channel
 * BCM2835_TIMEOUT_TIMER in this driver, we will only be concerned with bit
 * BIT(BCM2835_TIMEOUT_TIMER) of the status register.
*/
#define BCM2835_TIMER_CLEAR_IRQ BIT(BCM2835_TIMEOUT_TIMER)

#define BCM2835_TIMER_MAX_US UINT32_MAX

#define CLIENT_CH_START 1
#define MAX_TIMEOUTS SDDF_TIMER_MAX_CLIENTS
static uint64_t timeouts[MAX_TIMEOUTS];

static inline uint64_t get_ticks_in_ns(void)
{
    /* convert current value of free-running counter from microseconds to nanoseconds */
    uint64_t value_h = (uint64_t)timer_regs->chi;
    uint64_t value_l = (uint64_t)timer_regs->clo;
    uint64_t value_us = (value_h << 32) | value_l;
    return value_us * NS_IN_US;
}

void set_timeout(uint64_t ns)
{
    uint64_t value_us = ns / NS_IN_US;
    if (value_us > BCM2835_TIMER_MAX_US) {
        value_us = BCM2835_TIMER_MAX_US;
    }
    uint64_t timer_us = ((uint64_t)timer_regs->chi << 32) | timer_regs->clo;
    timer_regs->cn[BCM2835_TIMEOUT_TIMER] = (uint32_t)(timer_us + value_us);
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            sddf_notify(CLIENT_CH_START + i);
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
        uint64_t ns = next_timeout - curr_time;
        set_timeout(ns);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    /* Ack any IRQs that were delivered before the driver started. */
    sddf_irq_ack(device_resources.irqs[0].id);

    timer_regs = (bcm2835_timer_regs_t *)device_resources.regions[0].region.vaddr;

    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }
}

void notified(sddf_channel ch)
{
    assert(ch == device_resources.irqs[0].id);

    /* The status register is W1C (write 1 to clear) so we write 1 to clear the irq */
    timer_regs->cs = BCM2835_TIMER_CLEAR_IRQ;

    /* Process the timeout and handle the irq */
    uint64_t curr_time = get_ticks_in_ns();
    process_timeouts(curr_time);
    sddf_deferred_irq_ack(ch);
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    switch (seL4_MessageInfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = get_ticks_in_ns();
        seL4_SetMR(0, time_ns);
        return seL4_MessageInfo_new(0, 0, 0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns();
        uint64_t offset_ns = (uint64_t)(sddf_get_mr(0));
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_ns;
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
