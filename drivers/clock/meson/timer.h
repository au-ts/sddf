#include <stdint.h>
#include <microkit.h>

#define TIMER_CH    1
#define GET_TIME    0
#define SET_TIMEOUT 1

#define NS_IN_MS 1000000ULL
#define NS_IN_S  1000000000ULL

/**
 * Request a timeout via PPC into the passive timer driver.
 * Use the label to indicate this request.
 * @param timeout relative timeout in nanoseconds.
 */
void
timer_set_timeout(uint64_t timeout)
{
    microkit_mr_set(0, timeout);
    microkit_ppcall(TIMER_CH, microkit_msginfo_new(SET_TIMEOUT, 1));
}

/**
 * Request the time since start up via PPC into the passive timer driver.
 * Use the label to indicate this request.
 * @return the time in nanoseconds since start up.
 */
uint64_t
timer_time_now(void)
{
    microkit_ppcall(TIMER_CH, microkit_msginfo_new(GET_TIME, 0));
    uint64_t time_now = seL4_GetMR(0);
    return time_now;
}
