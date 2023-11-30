#include <microkit.h>
#include <stdint.h>
#include <arch/aarch64/generic_timer.h>
#include <minheap.h>
#include <frequency.h>
#include <printf.h>

/* All time units are in nano seconds */

#define MAX_TIMEOUTS 4096

#define GET_TIME 0
#define SET_TIMEOUT 1

static uint32_t freq;
static min_heap_t timeout_heap;
static heap_element_t timeout_heap_data[MAX_TIMEOUTS];


static uint64_t get_time()
{
    uint64_t ticks = generic_timer_get_ticks();
    return freq_cycles_and_hz_to_ns(ticks, freq);
}

static void set_timeout(uint64_t timeout)
{
    generic_timer_set_compare(freq_ns_and_hz_to_cycles(timeout, freq));
}

void
init(void)
{
    generic_timer_enable();
    generic_timer_unmask_irq();
    freq = generic_timer_get_freq();
    heap_init(&timeout_heap, timeout_heap_data, MAX_TIMEOUTS);
}

static void
handle_irq(microkit_channel ch)
{
    printf("ARM_TIMER_DRIVER|INFO: IRQ received!\n");
    heap_element_t min;
    heap_extract_min(&timeout_heap, min);
    
    microkit_notify(min.ch);
    
    set_timeout(min.key);
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
        case GET_TIME: {
            uint64_t time = get_time();
            seL4_SetMR(0, time);
            return microkit_msginfo_new(0, 1);
        }
        case SET_TIMEOUT: {
            uint64_t timeout_duration = (uint64_t)(seL4_GetMR(0));
            uint64_t cur_time = get_time();
            uint64_t timeout = cur_time + timeout_duration;
            heap_insert(&timeout_heap, (heap_element_t){.key = timeout, .ch = ch});
            uint64_t set_timeout;
            heap_get_min(&timeout_heap, &timeout);
            break;
        }
        default:
            break;
    }

    return microkit_msginfo_new(0, 0);
}




    // uint64_t time = get_time();
    // time += 5000000000;
    // generic_timer_set_compare(freq_ns_and_hz_to_cycles(time, freq));
    
    // uint64_t ticks;
    // uint64_t time_print;
    // // printf("freq: %d\n", freq);
    // for(int i = 0; true; i++) {
    //     ticks = generic_timer_get_ticks();
    //     time_print = freq_cycles_and_hz_to_ns(ticks, freq);
        
    //     if (i % 1000000 == 0) {
    //         printf("time: %d\n", time_print / 1000000000);
    //         printf("status: %d\n", generic_timer_status());
    //     }
    // }

    // heap_insert(&timeout_heap, (heap_element_t){.key = 300, .ch = 3});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 100, .ch = 1});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 200, .ch = 2});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 400, .ch = 4});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 600, .ch = 6});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 800, .ch = 8});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 700, .ch = 7});
    // heap_insert(&timeout_heap, (heap_element_t){.key = 500, .ch = 5});
    // heap_element_t min;
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);
    // heap_extract_min(&timeout_heap, &min);
    // printf("min: %llu\n", min.key);