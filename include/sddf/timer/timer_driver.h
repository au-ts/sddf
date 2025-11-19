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
