#include "include/motor/timer_queue.h"
// https://www.geeksforgeeks.org/c/queue-in-c/

void initializeQueue(Queue* q)
{
    q->front = -1;
    q->rear = 0;
}

bool isEmpty(Queue* q) { return (q->front == q->rear - 1); }

bool isFull(Queue* q) { return (q->rear == MAX_SIZE); }

void enqueue(Queue* q, int value)
{
    if (isFull(q)) {
        sddf_printf("Queue is full\n");
        return;
    }
    q->items[q->rear] = value;
    q->rear++;
}

void dequeue(Queue* q)
{
    if (isEmpty(q)) {
        sddf_printf("Queue is empty\n");
        return;
    }
    q->front++;
}

int pop(Queue* q)
{
    if (isEmpty(q)) {
        sddf_printf("Queue is empty\n");
        return -1; // return some default value or handle
                   // error differently
    }
    return q->items[q->front + 1];
}

void printQueue(Queue* q)
{
    if (isEmpty(q)) {
        sddf_printf("Queue is empty\n");
        return;
    }

    sddf_printf("Current Queue: ");
    for (int i = q->front + 1; i < q->rear; i++) {
        sddf_printf("%d ", q->items[i]);
    }
    sddf_printf("\n");
}