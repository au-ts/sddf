/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>

/**
 * Convert the tick count of a timer to nanoseconds, given the expected prescaler
 * and overflow counter. Prescaler can be set to 0 to ignore.
 *
 * Prescaler should be given as a multiplicand (i.e. each tick takes N ticks)
 * and a factor-based representation.
 *
 * @returns non-zero on failure.
 */
inline int tick_to_ns(uint64_t *result, uint64_t ticks, uint64_t prescaler, uint64_t clk_freq_hz)
{
    // seconds per tick = T_clk*prescaler = (f_clk^-1)*prescaler
    // ns per period = T_clk / 1e-9 = 1e9/f_clk = T_clk_nano
    // ns per tick = T_clk_nano * prescaler
    // ticks in ns = ticks * (T_clk_nano*prescaler)

    const uint64_t prescaler_adjusted = (prescaler == 0) ? 1 : prescaler + 1;

    // First: derive period to picosecond accuracy. This is necessary to
    // avoid losing precision with even somewhat fast clocks. This will
    // remain accurate up to impractically high speeds (>50GHz)
    const uint64_t T_clk_ps = PS_IN_S / clk_freq_hz;

    // Assumption: prescaler < T_ns < ticks_ns
    assert(T_clk_ps > 0);

    // return (ticks * NS_IN_S * prescaler_adjusted) / clk_freq_hz;
}

/**
 * Return number of ticks since driver startup using timekeeper timer.
 * NOTE: one round of timer @ 50MHz with prescaler of (1<<3)=4 lasts for 171.8
 *          seconds. Time resolution = 80ns per tick.
 */
inline uint64_t get_time_ns(void)
{
    uint64_t value_l = (uint64_t)(regs[TIMER_TIMEKEEPER].timer);
    uint64_t value_h = (uint64_t)timekeeper_overflow_count;
    uint64_t value_ticks = (value_h << 32) | value_l;

    return tick_to_ns(value_ticks, TIMEKEEPER_PRESCALER);
}
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
