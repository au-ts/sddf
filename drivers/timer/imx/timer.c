/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * This is a driver for the imx8m general purpose timer (GPT).
 * It is a 32 bit timer with a 12 bit prescaler.
 *
 * The input clock for this device is NOT fixed. A set of muxes
 * allows selection between one of the following clocks:
 * ~~ ipg_clk_24M: Fixed 24MHz crystal,
 * ~~ gpt_clk: external clock, frequency defined by board,
 * ~~ ipg_clk: peripheral clock, frequency defined by clock tree,
 * ~~ ipg_clk_32k: low-freq reference clock, fixed 32kHz frequency,
 * ~~ ipg_clkc_highfreq: high-freq reference clock, frequency depends on board.
 *
 * Uboot sets up the 24MHz clock for us, and we just trust that it's there.
 * TODO: use clock driver to set this up properly, enforced by sdfgen.
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/config.h>

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

#define GPT_FREQ   (24*MEGA)
#define GPT_PRESCALER (0)

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

static volatile uint32_t *gpt;
static uint32_t overflow_count;
static uint64_t target_timeout;

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

static void process_target_timeout(uint64_t curr_time)
{
    if (target_timeout <= curr_time) {
        sddf_notify(i);
        // Update "current" time page with virt
        set_shared_time_page(curr_time);
        target_timeout = UINT64_MAX;
        // No more work to do!
        return;
    }

    // Program timer otherwise
    if (next_timeout != UINT64_MAX && overflow_count == (next_timeout >> 32)) {
        gpt[OCR1] = (uint32_t)next_timeout;
        gpt[IR] |= 1;
    }
}

void notified(sddf_channel ch)
{
    if (ch != device_resources.irqs[0].id) {
        sddf_dprintf("TIMER DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
    }

    sddf_deferred_irq_ack(ch);

    uint32_t sr = gpt[SR];
    gpt[SR] = sr;

    if (sr & (1 << 5)) {
        overflow_count++;
    }

    if (sr & 1) {
        gpt[IR] &= ~1;
    }

    uint64_t curr_time = get_ticks();
    process_target_timeout(curr_time);
}

bool set_new_timeout(uint64_t timestamp)
{
    uint64_t curr_time = get_ticks();
    // Convert to ticks and set as target
    target_timeout = ns_to_tick_cached(timestamp, GPT_PRESCALER, (sddf_timer_freq_hz_t) GPT_FREQ);

    process_target_timeout(curr_time);
    return true;
}

uint64_t get_current_time(void)
{
    return (tick_to_ns_cached(get_ticks(), GPT_PRESCALER, (sddf_timer_freq_hz_t) GPT_FREQ));
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 1);
    assert(device_resources.num_regions == 1);

    target_timeout = UINT64_MAX;

    gpt = (volatile uint32_t *)device_resources.regions[0].region.vaddr;

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

    gpt[PR] = GPT_PRESCALER; // prescaler of 0 - use raw 24MHz clock.

    /* Now go passive! */
}
