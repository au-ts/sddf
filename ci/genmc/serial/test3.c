/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <stdlib.h>
#include <pthread.h>

#include <sddf/serial/queue.h>

#ifndef QUEUE_SIZE
#define QUEUE_SIZE 1
#endif

#ifndef PRODUCER
#define PRODUCER 1
#endif

#ifndef CONSUMER
#define CONSUMER 1
#endif

#ifndef BATCH_SIZE
#define BATCH_SIZE 1
#endif

#if PRODUCER < CONSUMER * BATCH_SIZE
#error "the producer size must be not less than the consumer size"
#endif

#if QUEUE_SIZE < BATCH_SIZE
#error "the queue size must be not less than the batch size"
#endif

static serial_queue_handle_t queue_handle;

void *producer(void *p)
{
    for (uint64_t i = 0; i < PRODUCER; i++) {
        while (serial_enqueue(&queue_handle, (char)i) != 0);
    }
    return NULL;
}

void *consumer(void *p)
{
    uint32_t local_head = 0;
    for (uint64_t i = 0; i < CONSUMER; i++) {
        for (uint64_t j = 0; j < BATCH_SIZE; j++) {
            char character;
            while (serial_dequeue_local(&queue_handle, &local_head, &character) != 0);
            assert(character == (char)(i * BATCH_SIZE + j));
        }
    }
    return NULL;
}

int main()
{
    serial_queue_t *queue = malloc(sizeof(serial_queue_t));
    if (queue == NULL) {
        exit(1);
    }
    queue->tail = 0;
    queue->head = 0;
    queue->producer_signalled = 0;

    char *data_region = malloc(QUEUE_SIZE * sizeof(char));
    if (data_region == NULL) {
        exit(1);
    }

    serial_queue_init(&queue_handle, queue, QUEUE_SIZE, data_region);

    pthread_t t1, t2;
    if (pthread_create(&t1, NULL, producer, NULL) != 0) {
        exit(1);
    }
    if (pthread_create(&t2, NULL, consumer, NULL) != 0) {
        exit(1);
    }

    pthread_join(t2, NULL);
    pthread_join(t1, NULL);

    free(data_region);
    free(queue);

    return 0;
}
