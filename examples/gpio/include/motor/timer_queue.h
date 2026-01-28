#include <microkit.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>

#define MAX_SIZE 100

// Defining the Queue structure
typedef struct {
    int items[MAX_SIZE];
    int front;
    int rear;
} Queue;


// Function to initialize the queue
void initializeQueue(Queue* q);

// Function to check if the queue is empty
bool isEmpty(Queue* q);

// Function to check if the queue is full
bool isFull(Queue* q);

// Function to add an element to the queue (Enqueue
// operation)
void enqueue(Queue* q, int value);

// Function to remove an element from the queue (Dequeue
// operation)
void dequeue(Queue* q);

// Function to get the element at the front of the queue
// (Peek operation)
int pop(Queue* q);

// Function to print the current queue
void printQueue(Queue* q);