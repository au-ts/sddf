/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

microkit_channel timer_channel;

void notified(microkit_channel ch)
{
    /*
     * In this example we only have a single possible channel,
     * so we know it's a notification from the driver telling
     * us that the timeout we set has gone off.
     */
    sddf_printf("CLIENT|INFO: Got a timeout!\n");
    /* Get the current time */
    uint64_t time = sddf_timer_time_now(timer_channel);
    sddf_printf("CLIENT|INFO: Now the time (in nanoseconds) is: %lu\n", time);
    /* Set another timeout */
    sddf_timer_set_timeout(timer_channel, NS_IN_S);
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");

    assert(timer_config_check_magic(&config));

    timer_channel = config.driver_id;

    // lets get the time!
    uint64_t time = sddf_timer_time_now(timer_channel);
    sddf_printf("CLIENT|INFO: The time now is: %lu\n", time);

    // lets set a timeout
    sddf_printf("CLIENT|INFO: Setting a time out for 1 second\n");
    sddf_timer_set_timeout(timer_channel, NS_IN_S);
}
