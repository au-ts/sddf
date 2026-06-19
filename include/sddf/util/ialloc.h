/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/util.h>

/**
 * This file provides an "index allocator" implementation that allocates
 * an ID to the caller which can later be to be retrieved and freed.
 * The implementation uses a fixed-size linked list to keep track of free indices.
 */

typedef struct ialloc {
    /* linked list pointing to the next free index. An index x is free if
     idxlist[x] != -1. The last free index in the list is set to the capacity of
     the index allocator. */
    uint32_t *idxlist;
    /* first free index */
    uint32_t head;
    /* last free index */
    uint32_t tail;
    /* number of allocated indices */
    uint32_t size;
    /* total number of indices. This must be < UINT32MAX to distinguish between
    indices being allocated */
    uint32_t capacity;
} ialloc_t;

/**
 * Check if all indices are used.
 *
 * @param ia pointer to the ialloc struct.
 *
 * @return true if index list is full, false otherwise.
 */
static inline bool ialloc_full(ialloc_t *ia)
{
    return ia->size == ia->capacity;
}

/**
 * Get the number of free indices available.
 *
 * @param ia pointer to the ialloc struct.
 *
 * @return number of free indices
 */
static inline uint32_t ialloc_num_free(ialloc_t *ia)
{
    return ia->capacity - ia->size;
}

/**
 * Check if an index is in use.
 *
 * @param ia pointer to the ialloc struct.
 * @param id index to check.
 *
 * @return true if index is in use and valid, false otherwise.
 */
static inline bool ialloc_in_use(ialloc_t *ia, uint32_t id)
{
    if (id >= ia->capacity || ia->idxlist[id] != -1) {
        return false;
    }
    return true;
}

/**
 * Allocate a free index.
 *
 * @param ia pointer to the ialloc struct.
 * @param id pointer to the index allocated.
 *
 * @return 0 on success, -1 if index list is full.
 */
static inline int ialloc_alloc(ialloc_t *ia, uint32_t *id)
{
    if (ialloc_full(ia)) {
        return -1;
    }

    *id = ia->head;
    if (ia->head == ia->tail) {
        /* List is now empty */
        ia->head = -1;
        ia->tail = -1;
    } else {
        ia->head = ia->idxlist[*id];
    }
    ia->idxlist[*id] = -1;
    ia->size++;
    return 0;
}

/**
 * Free an allocated index.
 *
 * @param ia pointer to the ialloc struct.
 * @param id active index to be freed.
 *
 * @return 0 on success, -1 if index is invalid.
 */
static inline int ialloc_free(ialloc_t *ia, uint32_t id)
{
    if (!ialloc_in_use(ia, id)) {
        return -1;
    }

    if (ialloc_full(ia)) {
        ia->head = id;
        ia->tail = id;
    } else {
        ia->idxlist[ia->tail] = id;
        ia->tail = id;
    }
    ia->idxlist[id] = ia->capacity;
    ia->size--;
    return 0;
}

/**
 * Initialise the index allocator. Allocates indices from 0 to size - 1 inclusive.
 *
 * @param ia pointer to the ialloc struct.
 * @param idxlist pointer to the linked list array storing the next free index.
 * @param capacity number of indices that can be allocated.
 */
static void ialloc_init(ialloc_t *ia, uint32_t *idxlist, uint32_t capacity)
{
    assert(capacity < -1);
    ia->idxlist = idxlist;
    ia->head = 0;
    ia->tail = capacity - 1;
    ia->size = 0;
    ia->capacity = capacity;
    for (uint32_t i = 0; i < capacity; i++) {
        ia->idxlist[i] = i + 1;
    }
}
