/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #define DEBUG_TIMER_DRIVER
#ifdef DEBUG_TIMER_DRIVER
#define LOG_TIMER_DRIVER(...) do{ sddf_dprintf("TIMER DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_TIMER_DRIVER(...) do{}while(0)
#endif

#define LOG_TIMER_DRIVER_ERR(...) do{ sddf_dprintf("TIMER DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

// Includes for timer drivers; implementing a priority heap array
// and structs for support of an arbitrary number of timeouts.
#define SDDF_TIMER_MAX_TIMEOUTS (128)

// Mult-shift cache
typedef struct ms_cache_entry {
    sddf_timer_freq_hz_t f_a;
    sddf_timer_freq_hz_t f_b;
    uint64_t mult;
    uint64_t shift;
} ms_cache_entry_t;

uint64_t tick_to_ns(uint64_t ticks, uint64_t prescaler, sddf_timer_freq_hz_t base_freq);
uint64_t ns_to_tick(uint64_t ns, uint64_t prescaler, sddf_timer_freq_hz_t base_freq);

// Representing one timeout operation in the queue.
typedef struct timeout {
    uint64_t timestamp;
    unsigned int client_channel;
} timeout_t;

// ### Timer (static) priority heap ###
typedef struct timer_heap {
    timeout_t timeouts[SDDF_TIMER_MAX_TIMEOUTS];
    size_t size;
} timer_heap_t;

void timer_heap_init(timer_heap_t *heap);

bool timer_heap_is_empty(const timer_heap_t *heap);

bool timer_heap_is_full(const timer_heap_t *heap);

size_t timer_heap_parent(size_t index);

size_t timer_heap_left_child(size_t index);

size_t timer_heap_right_child(size_t index);

void timer_heap_swap(timer_heap_t *heap, size_t i, size_t j);

// Heapify up - use after inserting
void timer_heap_heapify_up(timer_heap_t *heap, size_t index);

// Heapify down - use after popping head.
void timer_heap_heapify_down(timer_heap_t *heap, size_t index);

/**
 * Insert a new timeout into the timer priority heap.
 * @return true if successful, otherwise false
 */
bool timer_heap_insert(timer_heap_t *heap, uint64_t timestamp, unsigned int client_channel);

timeout_t *timer_heap_peek(timer_heap_t *heap);

bool timer_heap_pop(timer_heap_t *heap, timeout_t *result);

size_t timer_heap_size(const timer_heap_t *heap);
