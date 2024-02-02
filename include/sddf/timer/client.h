#pragma once

#include <microkit.h>
#include <stdint.h>

#define NS_IN_MS 1000000ULL
#define NS_IN_S  1000000000ULL
#define US_IN_MS 1000ULL
#define NS_IN_US 1000ULL

/**
 * Request a timeout via PPC into the passive timer driver.
 * Use the label to indicate this request.
 * @param microkit channel of timer driver.
 * @param timeout relative timeout in nanoseconds.
 */
void sddf_timer_set_timeout(microkit_channel channel, uint64_t timeout);

/**
 * Request the time since start up via PPC into the passive timer driver.
 * Use the label to indicate this request.
 * @param microkit channel of timer driver.
 * @return the time in nanoseconds since start up.
 */
uint64_t sddf_timer_time_now(microkit_channel channel);
