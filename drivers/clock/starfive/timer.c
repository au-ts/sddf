#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>

/*
 * The JH7110 SoC contains a timer with four 32-bit counters. Each one of these
 * counters is referred to as a "channel". These are not to be confused with
 * Microkit channels. Anything with a prefix STARFIVE_TIMER_* is to do with the
 * hardware.
 */
#define STARFIVE_TIMER_NUM_CHANNELS 4
// @ivanv: why not just use sizeof?
#define STARFIVE_TIMER_CHANNEL_REGS_SIZE 0x40

#ifndef STARFIVE_TIMER_CHANNEL
#define STARFIVE_TIMER_CHANNEL 1
#endif

#if STARFIVE_TIMER_CHANNEL >= STARFIVE_TIMER_NUM_CHANNELS
#error "Invalid StarFive timer device channel"
#endif

#define COUNTER_IRQ_CH 0
#define TIMEOUT_IRQ_CH 1

#define CLIENT_CH_START 2
#define MAX_TIMEOUTS 6

#define STARFIVE_TIMER_MAX_TICKS UINT32_MAX
#define STARFIVE_TIMER_MODE_CONTINUOUS 0
#define STARFIVE_TIMER_MODE_SINGLE 1
#define STARFIVE_TIMER_DISABLED 0
#define STARFIVE_TIMER_ENABLED 1
#define STARFIVE_TIMER_INTERRUPT_UNMASKED 0
#define STARFIVE_TIMER_INTERRUPT_MASKED 1
#define STARFIVE_TIMER_INTCLR_BUSY (1 << 1)

// @ivanv: TODO, comment this
#define STARFIVE_TIMER_TICKS_PER_SECOND 0x16e3600

typedef struct {
    /* Registers */
    // @ivanv: see what's up with this comment
    /* this register doesn't seem to do anything */
    uint32_t status;
    uint32_t ctrl;
    uint32_t load;
    uint32_t unknown1;
    uint32_t enable;
    uint32_t reload;
    uint32_t value;
    uint32_t unknown2;
    uint32_t intclr;
    uint32_t intmask;
} starfive_timer_regs_t;

uintptr_t timer_base;
static volatile starfive_timer_regs_t *counter_regs;
static volatile starfive_timer_regs_t *timeout_regs;
// @ivanv: comment
uint32_t counter_timer_elapses = 0;
uint32_t timeout_timer_elapses = 0;

/* Right now, we only service a single timeout per client.
 * This timeout array indicates when a timeout should occur,
 * indexed by client ID. */
static uint64_t timeouts[MAX_TIMEOUTS];

static uint64_t get_ticks_in_ns(void)
{
    /* the timer value counts down from the load value */
    uint64_t value_l = (uint64_t)(STARFIVE_TIMER_MAX_TICKS - counter_regs->value);
    uint64_t value_h = (uint64_t)counter_timer_elapses;

    /* Include unhandled interrupt in value_h */
    if (counter_regs->intclr == 1) {
        value_h += 1;
    }

    uint64_t value_ticks = (value_h << 32) | value_l;

    /* convert from ticks to nanoseconds */
    uint64_t value_whole_seconds = value_ticks / STARFIVE_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ticks = value_ticks % STARFIVE_TIMER_TICKS_PER_SECOND;
    uint64_t value_subsecond_ns =
        (value_subsecond_ticks * NS_IN_S) / STARFIVE_TIMER_TICKS_PER_SECOND;
    uint64_t value_ns = value_whole_seconds * NS_IN_S + value_subsecond_ns;

    return value_ns;
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(CLIENT_CH_START + i);
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
        // regs->mux &= ~TIMER_A_MODE;
        // regs->timer_a = next_timeout - curr_time;
        // regs->mux |= TIMER_A_EN;
    }
}

void notified(microkit_channel ch)
{
    if (ch != COUNTER_IRQ_CH && ch != TIMEOUT_IRQ_CH) {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
    }

    sddf_dprintf("got IRQ!\n");

    counter_timer_elapses += 1;

    while (counter_regs->intclr & STARFIVE_TIMER_INTCLR_BUSY) {
            /*
         * Hardware will not currently accept writes to this register.
         * Wait for this bit to be unset by hardware.
         */
    }

    counter_regs->intclr = 1;

    microkit_irq_ack_delayed(ch);

    uint64_t curr_time = get_ticks_in_ns();
    process_timeouts(curr_time);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = get_ticks_in_ns();
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks_in_ns();
        uint64_t offset_us = seL4_GetMR(0);
        timeouts[ch - CLIENT_CH_START] = curr_time + offset_us;
        process_timeouts(curr_time);
        break;
    }
    default:
        sddf_dprintf("TIMER DRIVER|LOG: Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo),
                     ch);
        break;
    }

    return microkit_msginfo_new(0, 0);
}

void init(void)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        timeouts[i] = UINT64_MAX;
    }

    counter_regs = (volatile starfive_timer_regs_t *) timer_base;
    timeout_regs = (volatile starfive_timer_regs_t *) timer_base + STARFIVE_TIMER_CHANNEL_REGS_SIZE * STARFIVE_TIMER_CHANNEL;

    timeout_regs->enable = STARFIVE_TIMER_DISABLED;
    timeout_regs->ctrl = STARFIVE_TIMER_MODE_CONTINUOUS;
    timeout_regs->load = STARFIVE_TIMER_MAX_TICKS;
    timeout_regs->intmask = STARFIVE_TIMER_INTERRUPT_UNMASKED;

    counter_regs->enable = STARFIVE_TIMER_DISABLED;
    counter_regs->ctrl = STARFIVE_TIMER_MODE_CONTINUOUS;
    counter_regs->load = STARFIVE_TIMER_MAX_TICKS;
    counter_regs->intmask = STARFIVE_TIMER_INTERRUPT_UNMASKED;

    counter_regs->enable = STARFIVE_TIMER_ENABLED;
}
