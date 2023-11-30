#include <stdbool.h>
#include <stddef.h>
#include <printf.h>
#include "include/minheap.h"

static void swap(heap_element_t *a, heap_element_t *b)
{
    heap_element_t temp = *a;
    *a = *b;
    *b = temp;
}

static void heapify_up(min_heap_t *heap, unsigned int index)
{
    if (index && heap->data[(index - 1) / 2].key > heap->data[index].key) {
        swap(&heap->data[index], &heap->data[(index - 1) / 2]);
        heapify_up(heap, (index - 1) / 2);
    }
}

static void heapify_down(min_heap_t *heap, unsigned int index)
{
    unsigned int smallest = index;
    unsigned int left = 2 * index + 1;
    unsigned int right = 2 * index + 2;

    if (left < heap->size && heap->data[left].key < heap->data[smallest].key)
        smallest = left;

    if (right < heap->size && heap->data[right].key < heap->data[smallest].key)
        smallest = right;

    if (smallest != index) {
        swap(&heap->data[index], &heap->data[smallest]);
        heapify_down(heap, smallest);
    }
}

void heap_init(min_heap_t *heap, heap_element_t *base, size_t max_size)
{
    heap->data = base;
    heap->size = 0;
    heap->max_size = max_size;
}

bool heap_insert(min_heap_t *heap, heap_element_t element)
{
    if (heap->size >= heap->max_size) {
        printf("Tried inserting into full heap\n");
        return false;
    }

    heap->data[heap->size] = element;
    heap->size++;
    heapify_up(heap, heap->size - 1);
    return true;
}

bool heap_extract_min(min_heap_t *heap, heap_element_t *element)
{
    if (heap_empty(heap)) {
        element = NULL;
        return false;
    }
    if (heap->size == 1) {
        heap->size--;
        *element = heap->data[0];
    } else {
        *element = heap->data[0];
        heap->data[0] = heap->data[heap->size - 1];
        heap->size--;
        heapify_down(heap, 0);
    }
    return true;
}
