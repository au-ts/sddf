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
    uint32_t *idxlist; /* linked list pointing to the next free index */
    uint32_t head; /* next free index */
    uint32_t tail; /* last free index */
    uint32_t num_free; /* number of free indices */
    uint32_t offset; /* offset to add to the index */
    uint32_t size; /* total number of indices */
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
    return ia->num_free == 0;
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
    return ia->num_free;
}

/**
 * Check if an index is in use.
 *
 * @param ia pointer to the ialloc struct.
 * @param id index to check.
 *
 * @return true if index is in use, false otherwise.
 */
static inline bool ialloc_in_use(ialloc_t *ia, uint32_t id)
{
    if (id >= ia->size + ia->offset || id < ia->offset) {
        return false;
    }
    return ia->idxlist[id - ia->offset] == -1;
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
    *id = ia->head + ia->offset;
    ia->head = ia->idxlist[ia->head];
    ia->idxlist[*id - ia->offset] = -1;
    ia->num_free--;
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
    if (id >= ia->size + ia->offset || id < ia->offset || !ialloc_in_use(ia, id)) {
        return -1;
    }
    if (ialloc_full(ia)) {
        // When index list is full, head and tail will point
        // to stale indices, so we have to restore it here.
        ia->head = id - ia->offset;
        ia->tail = id - ia->offset;
    } else {
        ia->idxlist[ia->tail] = id - ia->offset;
        ia->tail = id - ia->offset;
    }
    ia->num_free++;
    return 0;
}

/**
 * Initialise the index allocator. Allocates indices from 0 to size - 1 inclusive.
 *
 * @param ia pointer to the ialloc struct.
 * @param idxlist pointer to the linked list array storing the next free index.
 * @param size number of indices that can be allocated.
 */
static void ialloc_init(ialloc_t *ia, uint32_t *idxlist, uint32_t size)
{
    assert(size < -1);
    ia->idxlist = idxlist;
    ia->head = 0;
    ia->tail = size - 1;
    ia->num_free = size;
    ia->size = size;
    ia->offset = 0;
    for (uint32_t i = 0; i < size - 1; i++) {
        ia->idxlist[i] = i + 1;
    }
    ia->idxlist[size - 1] = -1;
}

/**
 * Initialise the index allocator. Allocates indices from offset to offset + size - 1 inclusive.
 *
 * @param ia pointer to the ialloc struct.
 * @param idxlist pointer to the linked list array storing the next free index.
 * @param size number of indices that can be allocated.
 * @param offset offset to add to the index.
 */
static void ialloc_init_with_offset(ialloc_t *ia, uint32_t *idxlist, uint32_t size, uint32_t offset)
{
    ialloc_init(ia, idxlist, size);
    ia->offset = offset;
}
