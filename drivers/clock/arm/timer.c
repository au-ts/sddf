#include <microkit.h>
#include <stdint.h>
#include <arch/generic_timer.h>
#include <frequency.h>
#include <printf.h>

void
init(void)
{
    generic_timer_enable();
    freq_t freq = generic_timer_get_freq();
    uint64_t ticks;
    uint64_t time;
    // printf("freq: %d\n", freq);
    for(int i = 0; true; i++) {
        ticks = generic_timer_get_ticks();
        time = freq_cycles_and_hz_to_ns(ticks, freq);
        
        if (i % 1000000 == 0) {
            printf("time: %d\n", time / 1000000000);
        }
    }
}

void
notified(microkit_channel ch)
{
}

seL4_MessageInfo_t
protected(microkit_channel ch, microkit_msginfo msginfo)
{
    return microkit_msginfo_new(0, 0);
}
