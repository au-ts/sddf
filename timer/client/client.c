#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/client.h>

#ifndef TIMER_CHANNEL
#error "TIMER_CHANNEL must be provided"
#endif

#define GET_TIME 0
#define SET_TIMEOUT 1

void
sddf_timer_set_timeout(uint64_t timeout)
{
    microkit_mr_set(0, timeout);
    microkit_ppcall(TIMER_CHANNEL, microkit_msginfo_new(SET_TIMEOUT, 1));
}

uint64_t
sddf_timer_time_now(void)
{
    microkit_ppcall(TIMER_CHANNEL, microkit_msginfo_new(GET_TIME, 0));
    uint64_t time_now = seL4_GetMR(0);
    return time_now;
}
