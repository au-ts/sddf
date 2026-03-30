/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/timer_virt.h>
#include <sddf/util/util.h>

#define ID_FIELD_BITS (sizeof(id_field_t) * 8)
#define ID_FIELD_FULL ((id_field_t)((1U << ID_FIELD_BITS) - 1))

static inline uint64_t generate_timeout_id(timer_heap_t *heap)
{
    // INVARIANT: heap is not full
    for (size_t i = 0; i < SDDF_TIMER_MAX_TIMEOUTS / ID_FIELD_BITS; i++) {
        if (heap->id_field[i] != ID_FIELD_FULL) {
            int first_free = __builtin_ctz((unsigned)(~heap->id_field[i] & ID_FIELD_FULL));
            heap->id_field[i] |= (id_field_t)(1U << first_free);
            return (i * ID_FIELD_BITS) + first_free;
        }
    }
    assert(false);
    __builtin_unreachable();
}

void free_timeout_id(timer_heap_t *heap, uint64_t id)
{
    // INVARIANT: this bit exists
    size_t byte_idx = id / ID_FIELD_BITS;
    uint8_t bit_idx = id % ID_FIELD_BITS;
    assert(byte_idx < SDDF_TIMER_MAX_TIMEOUTS / ID_FIELD_BITS);
    assert(heap->id_field[byte_idx] & (1U << bit_idx));
    heap->id_field[byte_idx] &= ~(1U << bit_idx);
}

static inline bool timeout_id_in_use(timer_heap_t *heap, uint64_t id)
{
    size_t byte_idx = id / ID_FIELD_BITS;
    uint8_t bit_idx = id % ID_FIELD_BITS;
    assert(byte_idx < SDDF_TIMER_MAX_TIMEOUTS / ID_FIELD_BITS);
    return ((heap->id_field[byte_idx] & (1U << bit_idx)) != 0);
}

bool timer_heap_delete(timer_heap_t *heap, uint64_t timer_id, unsigned int client)
{
    timeout_t *victim = NULL;
    // Traverse heap linearly from front->back
    for (size_t i = 0; i < SDDF_TIMER_MAX_TIMEOUTS; i++) {
        if (heap->timeouts[i].id == timer_id) {
            // check client is correct
            if (heap->timeouts[i].client_channel == client) {
                victim = &heap->timeouts[i];
                break;
            } else {
                // Wrong client!
                break;
            }
        } else {
            continue;
        }
    }

    if (victim == NULL) {
        return false;   // Not found or invalid
    }
    // Delete!
    free_timeout_id(heap, victim->id);
    *victim = heap->timeouts[heap->size - 1];
    heap->size--;
    timer_heap_heapify_down(heap, 0);
    return true;
}

void timer_heap_init(timer_heap_t *heap)
{
    heap->size = 0;
    // Init bit field for IDs
    assert(SDDF_TIMER_MAX_TIMEOUTS % 64 == 0);
    for (int i = 0; i < SDDF_TIMER_MAX_TIMEOUTS / 64; i++) {
        heap->id_field[i] = 0;
    }
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
 *
 * IMPORTANT: this method allocated a timeout ID.
 * @return true if successful, otherwise false
 */
bool timer_heap_insert(timer_heap_t *heap, uint64_t timestamp, uint64_t period,
                       unsigned int client_channel, uint64_t *timeout_id)
{
    if (timer_heap_is_full(heap)) {
        return false;
    }

    uint64_t id = generate_timeout_id(heap);
    heap->timeouts[heap->size].timestamp = timestamp;
    heap->timeouts[heap->size].period = period;
    heap->timeouts[heap->size].client_channel = client_channel;
    heap->timeouts[heap->size].id = id;
    timer_heap_heapify_up(heap, heap->size);
    heap->size++;

    *timeout_id = id;
    return true;
}

/**
 *  Given a timeout, re-insert it to the heap. This is intended for use
 *  with periodic timeouts that have just popped.
 *
 *  IMPORTANT: this method does NOT free timeout IDs! This must be done by the
 *  virt since periodic timeouts should preserve their ID on pop.
 *
 *  IMPORTANT: this method automatically adjusts the timestamp of the timeout.
 */
bool timer_heap_reinsert_periodic(timer_heap_t *heap, timeout_t *timeout)
{
    assert(timeout != NULL);
    assert(timeout_id_in_use(heap, timeout->id));
    assert(timeout->period != 0);
    heap->timeouts[heap->size].timestamp = timeout->timestamp + timeout->period;
    heap->timeouts[heap->size].period = timeout->period;
    heap->timeouts[heap->size].client_channel = timeout->client_channel;
    heap->timeouts[heap->size].id = timeout->id;
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
