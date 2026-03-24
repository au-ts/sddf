/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <sddf/timer/protocol.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #define DEBUG_TIMER_VIRT
#ifdef DEBUG_TIMER_VIRT
#define LOG_TIMER_VIRT(...) do{ sddf_dprintf("TIMER VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_TIMER_VIRT(...) do{}while(0)
#endif

#define LOG_TIMER_VIRT_ERR(...) do{ sddf_dprintf("TIMER VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

// PPC interface to driver
static inline void timer_virt_set_timeout(unsigned int channel, uint64_t timeout)
{
    sddf_set_mr(0, timeout);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_TIMER_SET_TIMEOUT, 0, 0, 1));
}

static inline uint64_t timer_virt_get_time(unsigned int channel)
{
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_TIMER_GET_TIME, 0, 0, 0));
    uint64_t time_now = sddf_get_mr(0);
    return time_now;
}

// Includes for timer drivers; implementing a priority heap array
// and structs for support of an arbitrary number of timeouts.
// Timeout count must be a multiple of sizeof(id_field_t).
#define SDDF_TIMER_MAX_TIMEOUTS (128)

// Representing one timeout operation in the queue.
typedef struct timeout {
    uint64_t timestamp;
    unsigned int client_channel;
    uint64_t period;
    uint64_t id;
} timeout_t;

// ### Timer (static) priority heap ###
typedef uint8_t id_field_t;
typedef struct timer_heap {
    timeout_t timeouts[SDDF_TIMER_MAX_TIMEOUTS];
    size_t size;
    id_field_t id_field[SDDF_TIMER_MAX_TIMEOUTS / sizeof(id_field_t)];
} timer_heap_t;

inline void free_timeout_id(timer_heap_t *heap, uint64_t id);

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

bool timer_heap_reinsert_periodic(timer_heap_t *heap, timeout_t *timeout);

/**
 * Delete a timeout to cancel it.
 */
bool timer_heap_delete(timer_heap_t *heap, uint64_t timer_id);

timeout_t *timer_heap_peek(timer_heap_t *heap);

bool timer_heap_pop(timer_heap_t *heap, timeout_t *result);

size_t timer_heap_size(const timer_heap_t *heap);
