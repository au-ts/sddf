#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

// @ericc: This implementation is not a fully generic miheap for now because its simpler to implement.
// We can make this more generic later by changing heap_element_t to store an index to some metadata structure instead
// of some uint64_t value. Will need to bookkeep the metadata structure when we insert/extract from heap.

// Structure for each heap element
typedef struct {
    uint64_t key;        // The key used for ordering in the min heap
    uint64_t value;      // Client-specific value
} heap_element_t;

// Structure for the min heap
typedef struct {
    heap_element_t *data;      // Pointer to the array of heap elements
    uint32_t size;             // Current number of elements in the heap
    uint32_t max_size;         // Maximum size of the heap
} min_heap_t;

/**
 * Initializes the min heap with a given maximum size and the base array pointer.
 * 
 * @param heap Pointer to the min_heap_t structure.
 * @param base Pointer to an array of heap_element_t structures.
 * @param max_size The maximum number of elements the heap can hold.
 */
void heap_init(min_heap_t *heap, heap_element_t *base, size_t max_size);

/**
 * Checks if the heap is empty.
 * 
 * @param heap Pointer to the min_heap_t structure.
 * @return True if the heap is empty; otherwise false.
 */
static inline bool heap_empty(min_heap_t *heap)
{
    return heap->size == 0;
}

/**
 * Checks if the heap is full.
 * 
 * @param heap Pointer to the min_heap_t structure.
 * @return True if the heap is full; otherwise false.
 */
static inline bool heap_full(min_heap_t *heap)
{
    return heap->size == heap->max_size;
}

/**
 * Inserts a new element into the min heap.
 * 
 * @param heap Pointer to the min_heap_t structure.
 * @param element The heap_element_t to be inserted into the heap.
 * @return True if the element was inserted successfully; otherwise false.
 */
bool heap_insert(min_heap_t *heap, heap_element_t element);

/**
 * Extracts and returns the minimum element from the heap.
 * 
 * @param heap Pointer to the min_heap_t structure.
 * @param element Pointer to the heap_element_t structure to store the minimum
 * element.
 * @return True if the minimum element was extracted successfully; otherwise
 * false.
 */
bool heap_extract_min(min_heap_t *heap, heap_element_t *element);

/**
 * Retrieves the minimum element from the heap without removing it.
 * 
 * @param heap Pointer to the min_heap_t structure.
 * @param element Pointer to the heap_element_t structure to store the minimum
 * element.
 * @return True if the minimum element was retrieved successfully; otherwise
 * false.
 */
static inline bool heap_get_min(min_heap_t *heap, heap_element_t *element)
{
    if (heap_empty(heap)) {
        element = NULL;
        return false;
    }
    *element = heap->data[0];
    return true;
}
