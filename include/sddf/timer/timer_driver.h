/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

// Includes for timer drivers; implementing a priority heap array
// and structs for support of an arbitrary number of timeouts.

#define SDDF_TIMER_MAX_TIMEOUTS (128)

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

static inline void timer_heap_init(timer_heap_t *heap)
{
    heap->size = 0;
}

static inline bool timer_heap_is_empty(const timer_heap_t *heap)
{
    return heap->size == 0;
}

static inline bool timer_heap_is_full(const timer_heap_t *heap)
{
    return (heap->size >= SDDF_TIMER_MAX_TIMEOUTS);
}

static inline size_t timer_heap_parent(size_t index)
{
    return (index - 1) / 2;
}

static inline size_t timer_heap_left_child(size_t index)
{
    return 2 * index + 1;
}

static inline size_t timer_heap_right_child(size_t index)
{
    return 2 * index + 2;
}

static inline void timer_heap_swap(timer_heap_t *heap, size_t i, size_t j)
{
    timeout_t temp = heap->timeouts[i];
    heap->timeouts[i] = heap->timeouts[j];
    heap->timeouts[j] = temp;
}

// Heapify up - use after inserting
static inline void timer_heap_heapify_up(timer_heap_t *heap, size_t index)
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
static inline void timer_heap_heapify_down(timer_heap_t *heap, size_t index)
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
static inline bool timer_heap_insert(timer_heap_t *heap, uint64_t timestamp, unsigned int client_channel)
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

static inline timeout_t *timer_heap_peek(timer_heap_t *heap)
{
    if (timer_heap_is_empty(heap)) {
        return NULL;
    }
    return &heap->timeouts[0];
}

static inline bool timer_heap_pop(timer_heap_t *heap, timeout_t *result)
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

static inline size_t timer_heap_size(const timer_heap_t *heap)
{
    return heap->size;
}
