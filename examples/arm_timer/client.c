#include <microkit.h>
#include <sddf/timer/client.h>
#include <printf.h>

#define TIMER_CH 1

void
init(void)
{
    // get time
    uint64_t time = sddf_timer_time_now();
    printf("ARM_TIMER_CLIENT|INFO: The time now is: %llu\n", time);

    // set timeouts
    printf("ARM_TIMER_CLIENT|INFO: Setting a time out for 2 seconds\n");
    sddf_timer_set_timeout(NS_IN_S * 2);
    printf("ARM_TIMER_CLIENT|INFO: Setting a time out for 6 seconds\n");
    sddf_timer_set_timeout(NS_IN_S * 6);
}

void
notified(microkit_channel ch)
{
    if (ch == TIMER_CH) {
        printf("ARM_TIMER_CLIENT|INFO: Timeout received!\n");
    }
}
