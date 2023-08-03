#include <stdint.h>

#define TIMER_CH    1
#define GET_TIME    0
#define SET_TIMEOUT 1

#define NS_IN_MS 1000000ULL
#define NS_IN_S  1000000000ULL

/**
 * Request a timeout via RPC into the passive timer driver.
 * Use the label to indicate this request.
 * @param timeout relative timeout in nanoseconds.
 */
void
set_timeout(uint64_t timeout)
{
    sel4cp_mr_set(0, timeout);
    sel4cp_ppcall(TIMER_CH, sel4cp_msginfo_new(SET_TIMEOUT, 1));
}

/**
 * Request the time since start up via RPC into the passive timer driver.
 * Use the label to indicate this request.
 * @return the time in nanoseconds since start up.
 */
uint64_t
time_now(void)
{
    sel4cp_ppcall(TIMER_CH, sel4cp_msginfo_new(GET_TIME, 0));
    uint64_t time_now = seL4_GetMR(0);
    return time_now;
}
