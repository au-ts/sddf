/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Very basic timer driver. Currently only permtis
 * a maximum of a single timeout per client for simplicity.
 *
 * Interfaces for clients:
 * microkit_ppcall() with label 0 is a request to get the current time.
 * with a 1 is a request to set a timeout.
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>

#define GPT_STATUS_REGISTER_CLEAR 0x3F
#define CR 0
#define PR 1
#define SR 2
#define IR 3
#define OCR1 4
#define OCR2 5
#define OCR3 6
#define ICR1 7
#define ICR2 8
#define CNT 9

#define MAX_TIMEOUTS 6

#define IRQ_CH 0

#define GPT_FREQ   (12u)

uintptr_t gpt_regs;
static volatile uint32_t *gpt;
static uint32_t overflow_count;
static uint64_t timeouts[MAX_TIMEOUTS];

static uint64_t get_ticks(void)
{
    uint64_t overflow = overflow_count;
    uint32_t sr1 = gpt[SR];
    uint32_t cnt = gpt[CNT];
    uint32_t sr2 = gpt[SR];
    if ((sr2 & (1 << 5)) && (!(sr1 & (1 << 5)))) {
        /* rolled-over during - 64-bit time must be the overflow */
        cnt = gpt[CNT];
        overflow++;
    }
    return (overflow << 32) | cnt;
}

static void process_timeouts(uint64_t curr_time)
{
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] <= curr_time) {
            microkit_notify(i);
            timeouts[i] = UINT64_MAX;
        }
    }

    uint64_t next_timeout = UINT64_MAX;
    for (int i = 0; i < MAX_TIMEOUTS; i++) {
        if (timeouts[i] < next_timeout) {
            next_timeout = timeouts[i];
        }
    }

    if (next_timeout != UINT64_MAX && overflow_count == (next_timeout >> 32)) {
        gpt[OCR1] = (uint32_t)next_timeout;
        gpt[IR] |= 1;
    }
}

void notified(microkit_channel ch)
{
    if (ch != IRQ_CH) {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
    }

    microkit_deferred_irq_ack(ch);

    uint32_t sr = gpt[SR];
    gpt[SR] = sr;

    if (sr & (1 << 5)) {
        overflow_count++;
    }

    if (sr & 1) {
        gpt[IR] &= ~1;
    }

    uint64_t curr_time = get_ticks();
    process_timeouts(curr_time);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        uint64_t time_ns = (get_ticks() / (uint64_t)GPT_FREQ) * NS_IN_US;
        seL4_SetMR(0, time_ns);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_SET_TIMEOUT: {
        uint64_t curr_time = get_ticks();
        uint64_t offset_ticks = (seL4_GetMR(0) / NS_IN_US) * (uint64_t)GPT_FREQ;
        timeouts[ch] = curr_time + offset_ticks;
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

    gpt = (volatile uint32_t *) gpt_regs;

    /* Disable GPT. */
    gpt[CR] = 0;
    gpt[SR] = GPT_STATUS_REGISTER_CLEAR;

    /* Configure GPT. */
    gpt[CR] = 0 | (1 << 15); /* Reset the GPT */
    /* SWR will be 0 when the reset is done */
    while (gpt[CR] & (1 << 15));

    uint32_t cr = (
                      (1 << 9) | // Free run mode
                      (1 << 6) | // Peripheral clocks
                      (1) // Enable
                  );

    gpt[CR] = cr;

    gpt[IR] = (
                  (1 << 5) // rollover interrupt
              );

    gpt[PR] = 1; // prescaler.

    /* Now go passive! */
}
