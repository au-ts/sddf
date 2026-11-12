/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>

timer_client_config_t *timer_config;

void notified(sddf_channel ch)
{
#ifdef MULTIKERNEL
    sddf_multikernel_ack(ch);
#endif
    /*
     * In this example we only have a single possible channel,
     * so we know it's a notification from the driver telling
     * us that the timeout we set has gone off.
     */
    /* Get the current time */
    uint64_t time = sddf_timer_time_now();
    /* Set another timeout */
    sddf_timer_set_timeout(timer_config, NS_IN_S);

    sddf_printf("CLIENT|INFO: Got a timeout!\n");
    sddf_printf("CLIENT|INFO: The time (in nanoseconds) was: %lu\n", time);
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");

    assert(timer_config_check_magic(timer_config));

    // lets get the time!
    uint64_t time = sddf_timer_time_now();
    // lets set a timeout
    sddf_timer_set_timeout(timer_config, NS_IN_S);

    sddf_printf("CLIENT|INFO: The time was is: %lu\n", time);
    sddf_printf("CLIENT|INFO: Set a time out for 1 second\n");
}
