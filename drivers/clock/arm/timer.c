#include <microkit.h>
#include <stdint.h>
#include <arch/aarch64/generic_timer.h>
#include <minheap.h>
#include <frequency.h>
#include <printf.h>

/* All time units are in nano seconds */

#define IRQ_CH 0
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
    freq = generic_timer_get_freq();
    generic_timer_enable();
    generic_timer_set_compare(UINT64_MAX);
    heap_init(&timeout_heap, timeout_heap_data, MAX_TIMEOUTS);    
}

static void
handle_irq(microkit_channel ch)
{   
    if (heap_empty(&timeout_heap)) {
        // Could receive an IRQ on PD init when heap is empty, do nothing just ack it
        // After init this should never happen, and would be considered an error
        printf("ARM_TIMER_DRIVER|INFO: received IRQ when heap is empty\n");
        generic_timer_set_compare(UINT64_MAX);
        return;
    }

    heap_element_t min;
    heap_extract_min(&timeout_heap, &min);
    
    microkit_notify(min.ch);

    if (heap_empty(&timeout_heap)) {
        generic_timer_set_compare(UINT64_MAX);
        return;
    } else {
        heap_get_min(&timeout_heap, &min);
        set_timeout(min.key);
    }
}

void
notified(microkit_channel ch)
{
    if (ch == IRQ_CH) {
        handle_irq(ch);
        microkit_irq_ack_delayed(ch);
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
            if (heap_full(&timeout_heap)) {
                // @ericc: Drop the request if heap is full
                printf("ARM_TIMER_DRIVER|ERROR: timeout heap full\n");
                break;
            }
            uint64_t timeout_duration = (uint64_t)(seL4_GetMR(0));
            uint64_t cur_time = get_time();
            uint64_t timeout = cur_time + timeout_duration;
            heap_insert(&timeout_heap, (heap_element_t){.key = timeout, .ch = ch});
            
            heap_element_t min;
            heap_get_min(&timeout_heap, &min);
            set_timeout(min.key);
            break;
        }
        default:
            break;
    }
    return microkit_msginfo_new(0, 0);
}
