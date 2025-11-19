/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>

/**
 * Convert the tick count of a timer to nanoseconds, given the expected prescaler.
 * Prescaler can be set to 0 to ignore.
 *
 * Prescaler should be given as an exponent, i.e. prescaler counter counts to 2^N,
 * provide N.
 *
 * This is based on `clocksource_cyc2ns` from the Linux kernel.
 *
 * @param conf timeconv_config_t with factors calculated from helper script
 * @param uint64_t ticks to convert
 * @param uint64_t prescaler exponent
 * @returns non-zero on failure.
 */
inline uint64_t tick_to_ns(timeconv_config_t *conf, uint64_t ticks, uint64_t prescaler)
{
    // Keep total shift reasonable.
    assert(conf->shift + prescaler < 32);
    return ((uint64_t) ticks * conf->mult) >> (conf->shift + prescaler);
}

inline uint64_t ns_to_tick(


void timer_heap_init(timer_heap_t *heap)
{
    heap->size = 0;
}

bool timer_heap_is_empty(const timer_heap_t *heap)
{
    return heap->size == 0;
}

bool timer_heap_is_full(const timer_heap_t *heap)
{
    return (heap->size >= SDDF_TIMER_MAX_TIMEOUTS);
}

size_t timer_heap_parent(size_t index)
{
    return (index - 1) / 2;
}

size_t timer_heap_left_child(size_t index)
{
    return 2 * index + 1;
}

size_t timer_heap_right_child(size_t index)
{
    return 2 * index + 2;
}

void timer_heap_swap(timer_heap_t *heap, size_t i, size_t j)
{
    timeout_t temp = heap->timeouts[i];
    heap->timeouts[i] = heap->timeouts[j];
    heap->timeouts[j] = temp;
}

// Heapify up - use after inserting
void timer_heap_heapify_up(timer_heap_t *heap, size_t index)
{
    while (index > 0) {
        size_t parent_idx = timer_heap_parent(index);
        if (heap->timeouts[index].timestamp >= heap->timeouts[parent_idx].timestamp) {
            break;
        }
        timer_heap_swap(heap, index, parent_idx);
        index = parent_idx;
    }
}

// Heapify down - use after popping head.
void timer_heap_heapify_down(timer_heap_t *heap, size_t index)
{
    while (timer_heap_left_child(index) < heap->size) {
        size_t left = timer_heap_left_child(index);
        size_t right = timer_heap_right_child(index);
        size_t smallest = index;

        if (heap->timeouts[left].timestamp < heap->timeouts[smallest].timestamp) {
            smallest = left;
        }

        if (right < heap->size && heap->timeouts[right].timestamp < heap->timeouts[smallest].timestamp) {
            smallest = right;
        }

        if (smallest == index) {
            break;
        }

        timer_heap_swap(heap, index, smallest);
        index = smallest;
    }
}

/**
 * Insert a new timeout into the timer priority heap.
 * @return true if successful, otherwise false
 */
bool timer_heap_insert(timer_heap_t *heap, uint64_t timestamp, unsigned int client_channel)
{
    if (timer_heap_is_full(heap)) {
        return false;
    }

    heap->timeouts[heap->size].timestamp = timestamp;
    heap->timeouts[heap->size].client_channel = client_channel;
    timer_heap_heapify_up(heap, heap->size);
    heap->size++;

    return true;
}

timeout_t *timer_heap_peek(timer_heap_t *heap)
{
    if (timer_heap_is_empty(heap)) {
        return NULL;
    }
    return &heap->timeouts[0];
}

bool timer_heap_pop(timer_heap_t *heap, timeout_t *result)
{
    if (timer_heap_is_empty(heap)) {
        return false;
    }

    *result = heap->timeouts[0];
    heap->timeouts[0] = heap->timeouts[heap->size - 1];
    heap->size--;
    timer_heap_heapify_down(heap, 0);

    return true;
}

size_t timer_heap_size(const timer_heap_t *heap)
{
    return heap->size;
}
