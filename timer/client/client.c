#include <stdint.h>
#include <microkit.h>
#include <sddf/timer/client.h>

#define GET_TIME 0
#define SET_TIMEOUT 1

void
sddf_timer_set_timeout(microkit_channel channel, uint64_t timeout)
{
    microkit_mr_set(0, timeout);
    microkit_ppcall(channel, microkit_msginfo_new(SET_TIMEOUT, 1));
}

uint64_t
sddf_timer_time_now(microkit_channel channel)
{
    microkit_ppcall(channel, microkit_msginfo_new(GET_TIME, 0));
    uint64_t time_now = seL4_GetMR(0);
    return time_now;
}