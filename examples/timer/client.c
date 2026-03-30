/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>
#include <sddf/util/si_units.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

sddf_channel timer_channel;

/* Test configuration */
#define DELAY_RELATIVE_NS   (100000000ULL)   /* 100 ms */
#define DELAY_ABSOLUTE_NS   (200000000ULL)   /* 200 ms */
#define PERIOD_NS           (50000000ULL)    /* 50 ms */
#define TOLERANCE_NS        (1000000ULL)     /* 1 ms tolerance for early detection */
#define PERIODIC_COUNT_MAX  (10)

typedef enum {
    STAGE_RELATIVE,
    STAGE_ABSOLUTE,
    STAGE_PERIODIC,
    STAGE_DONE
} test_stage_t;

static test_stage_t stage = STAGE_RELATIVE;
static uint64_t expected_time = 0;
static uint64_t timeout_id = 0;
static int periodic_count = 0;
static uint64_t periodic_period = 0;

void notified(sddf_channel ch)
{
    uint64_t now = sddf_timer_time_now(timer_channel);

    // Check for early interrupt
    if (now < (expected_time - TOLERANCE_NS)) {
        sddf_printf("CLIENT|ERROR: Timeout fired early! Expected %lu, got %lu (delta %ld ns)\n",
                    expected_time, now, (int64_t)(expected_time - now));
    }

    switch (stage) {
        case STAGE_RELATIVE: {
            sddf_printf("CLIENT|INFO: Relative timeout completed at %lu ns\n", now);

            stage = STAGE_ABSOLUTE;
            expected_time = now + DELAY_ABSOLUTE_NS;

            sddf_printf("CLIENT|INFO: Setting absolute timeout for %lu ns\n", expected_time);
            int err = sddf_timer_set_timeout(timer_channel, expected_time, 0, &timeout_id);
            if (err) {
                sddf_printf("CLIENT|ERROR: Failed to set absolute timeout: %d\n", err);
            }
            break;
        }

        case STAGE_ABSOLUTE: {
            sddf_printf("CLIENT|INFO: Absolute timeout completed at %lu ns\n", now);

            stage = STAGE_PERIODIC;
            periodic_count = 0;
            periodic_period = PERIOD_NS;
            expected_time = now + periodic_period;

            sddf_printf("CLIENT|INFO: Setting periodic timeout (period %lu ns), first firing at %lu\n",
                        periodic_period, expected_time);
            int err = sddf_timer_set_timeout(timer_channel, expected_time, periodic_period, &timeout_id);
            if (err) {
                sddf_printf("CLIENT|ERROR: Failed to set periodic timeout: %d\n", err);
            }
            break;
        }

        case STAGE_PERIODIC: {
            periodic_count++;
            sddf_printf("CLIENT|INFO: Periodic timeout %d/%d at %lu ns\n",
                        periodic_count, PERIODIC_COUNT_MAX, now);

            if (periodic_count >= PERIODIC_COUNT_MAX) {
                sddf_printf("CLIENT|INFO: Cancelling periodic timeout after %d firings\n",
                            periodic_count);
                int err = sddf_timer_cancel_timeout(timer_channel, timeout_id);
                if (err) {
                    sddf_printf("CLIENT|ERROR: Failed to cancel timeout: %d\n", err);
                } else {
                    sddf_printf("CLIENT|INFO: Timeout cancelled successfully\n");
                }
                stage = STAGE_DONE;
                sddf_printf("CLIENT|INFO: Finished testing timer features! Proceeding to counting the time.\n");
                err = sddf_timer_set_timeout(timer_channel, 0, NS_IN_S, &timeout_id);
                if (err) {
                    sddf_printf("CLIENT|ERROR: failed to start time count!\n");
                }
            } else {
                // Update expectation for next periodic firing
                expected_time += periodic_period;
            }
            break;
        }

        case STAGE_DONE:
            sddf_printf("CLIENT|INFO: The time is %llu seconds.\n",
                        read_timeout_stamp_page((uint64_t *)config.time_page.vaddr) / NS_IN_S);
            break;
    }
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting timer client test\n");

    assert(timer_config_check_magic(&config));
    timer_channel = config.virt_id;

    uint64_t now = sddf_timer_time_now(timer_channel);
    sddf_printf("CLIENT|INFO: Current time %lu ns\n", now);

    // start first test stage
    sddf_printf("CLIENT|INFO: Stage 1 - Setting relative timeout (%llu ns)\n", DELAY_RELATIVE_NS);
    expected_time = now + DELAY_RELATIVE_NS;

    int err = sddf_timer_set_relative_timeout(timer_channel, DELAY_RELATIVE_NS, &timeout_id);
    if (err) {
        sddf_printf("CLIENT|ERROR: Failed to set relative timeout: %d\n", err);
    }
}
