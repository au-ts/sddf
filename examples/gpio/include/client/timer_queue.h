#include <microkit.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>

#define MAX_SIZE 100
// https://www.geeksforgeeks.org/c/c-program-to-implement-priority-queue/

// Defining the Queue structure
typedef struct {
    uint64_t items[MAX_SIZE];
    int vals[MAX_SIZE];
    int size;
} PriorityQueue;


// Define heapifyUp function to maintain heap property
// during insertion
void heapify_up(PriorityQueue* pq, int index);

// Define enqueue function to add an item to the queue
void enqueue(PriorityQueue* pq, uint64_t value, int id);

// Define heapifyDown function to maintain heap property
// during deletion
void heapify_down(PriorityQueue* pq, int index);

// Remove the top id from the queue
int dequeue(PriorityQueue* pq);

// Get the top id from the queue
int peek(PriorityQueue* pq);