#include "include/motor/timer_queue.h"

void swap(int* a, int* b)
{
    int temp = *a;
    *a = *b;
    *b = temp;
}

void heapifyUp(PriorityQueue* pq, int index)
{
    if (index
        && pq->items[(index - 1) / 2] > pq->items[index]) {
        swap(&pq->items[(index - 1) / 2],
             &pq->items[index]);
        swap(&pq->vals[(index - 1) / 2],
             &pq->vals[index]);
        heapifyUp(pq, (index - 1) / 2);
    }
}
void enqueue(PriorityQueue* pq, uint64_t value, char symbol)
{
    if (pq->size == MAX) {
        sddf_printf("Priority queue is full\n");
        return;
    }

    pq->items[pq->size++] = value;
    pq->vals[pq->size++] = symbol;
    heapifyUp(pq, pq->size - 1);
}

void heapifyDown(PriorityQueue* pq, int index)
{
    int smallest = index;
    int left = 2 * index + 1;
    int right = 2 * index + 2;

    if (left < pq->size
        && pq->items[left] < pq->items[smallest])
        smallest = left;

    if (right < pq->size
        && pq->items[right] < pq->items[smallest])
        smallest = right;

    if (smallest != index) {
        swap(&pq->items[index], &pq->items[smallest]);
        swap(&pq->vals[index], &pq->vals[smallest]);
        heapifyDown(pq, smallest);
    }
}

char dequeue(PriorityQueue* pq)
{
    if (!pq->size) {
        sddf_printf("Priority queue is empty\n");
        return -1;
    }

    char value = pq->vals[0];
    pq->items[0] = pq->items[--pq->size];
    pq->vals[0] = pq->vals[--pq->size];

    heapifyDown(pq, 0);
    return value;
}

char peek(PriorityQueue* pq)
{
    if (!pq->size) {
        sddf_printf("Priority queue is empty\n");
        return 0;
    }
    return pq->vals[0];
}