#include <microkit.h>
#include <stdint.h>
#include <arch/generic_timer.h>
#include <frequency.h>
#include <printf.h>

/* All time units are in nano seconds */

#define MAX_TIMEOUTS 6

#define GET_TIME 0
#define SET_TIMEOUT 1

static uint32_t freq;
// static uint64_t timeouts[MAX_TIMEOUTS];


static uint64_t get_time()
{
    uint64_t ticks = generic_timer_get_ticks();
    return freq_cycles_and_hz_to_ns(ticks, freq);
}

// int set_timeout(void *data, uint64_t ns, timeout_type_t type)
// {
//     generic_ltimer_t *ltimer = data;
//     if (type == TIMEOUT_PERIODIC) {
//         ltimer->period = ns;
//     } else {
//         ltimer->period = 0;
//     }

//     uint64_t time;
//     int error = get_time(data, &time);
//     if (type != TIMEOUT_ABSOLUTE) {
//         if (error) {
//             return error;
//         }
//         ns += time;
//     }

//     if (time > ns) {
//         return ETIME;
//     }
//     generic_timer_set_compare(freq_ns_and_hz_to_cycles(ns, ltimer->freq));

//     return 0;
// }


void
init(void)
{
    generic_timer_enable();
    generic_timer_unmask_irq();
    freq = generic_timer_get_freq();
    uint64_t time = get_time();
    time += 5000000000;
    generic_timer_set_compare(freq_ns_and_hz_to_cycles(time, freq));
    // uint64_t ticks;
    // uint64_t time;
    // // printf("freq: %d\n", freq);
    // for(int i = 0; true; i++) {
    //     ticks = generic_timer_get_ticks();
    //     time = freq_cycles_and_hz_to_ns(ticks, freq);
        
    //     if (i % 1000000 == 0) {
    //         printf("time: %d\n", time / 1000000000);
    //     }
    // }
}

static void
handle_irq(microkit_channel ch)
{
    printf("ARM_TIMER_DRIVER|INFO: IRQ received!\n");
}

void
notified(microkit_channel ch)
{
    if (ch == GENERIC_TIMER_PCNT_IRQ) {
        handle_irq(ch);
    } else {
        printf("ARM_TIMER_DRIVER|ERROR: unexpected notification\n");
    }
}

seL4_MessageInfo_t
protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {
        case GET_TIME:
            break;
        case SET_TIMEOUT:
            break;
        default:
            break;
    }

    return microkit_msginfo_new(0, 0);
}
