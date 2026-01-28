#include <microkit.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>

#define MAX 100

// Defining the Queue structure
typedef struct {
    int items[MAX];
    int size;
} PriorityQueue;


// Define heapifyUp function to maintain heap property
// during insertion
void heapifyUp(PriorityQueue* pq, int index);

// Define enqueue function to add an item to the queue
void enqueue(PriorityQueue* pq, int value);

// Define heapifyDown function to maintain heap property
// during deletion
int heapifyDown(PriorityQueue* pq, int index);

// Define dequeue function to remove an item from the queue
int dequeue(PriorityQueue* pq);

// Define peek function to get the top item from the queue
int peek(PriorityQueue* pq);