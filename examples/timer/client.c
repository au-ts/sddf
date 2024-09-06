/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/client.h>
#include <sddf/util/printf.h>

#define TIMER_CHANNEL 1

void notified(microkit_channel ch)
{
    /*
     * In this example we only have a single possible channel,
     * so we know it's a notification from the driver telling
     * us that the timeout we set has gone off.
     */
    sddf_printf("CLIENT|INFO: Got a timeout!\n");
    /* Get the current time */
    uint64_t time = sddf_timer_time_now(TIMER_CHANNEL);
    sddf_printf("CLIENT|INFO: Now the time (in nanoseconds) is: %lu\n", time);
    /* Set another timeout */
    sddf_timer_set_timeout(TIMER_CHANNEL, NS_IN_S);
}

void init(void)
{
    // lets get the time!
    uint64_t time = sddf_timer_time_now(TIMER_CHANNEL);
    sddf_printf("CLIENT|INFO: The time now is: %lu\n", time);

    // lets set a timeout
    sddf_printf("CLIENT|INFO: Setting a time out for 1 second\n");
    sddf_timer_set_timeout(TIMER_CHANNEL, NS_IN_S);
}
