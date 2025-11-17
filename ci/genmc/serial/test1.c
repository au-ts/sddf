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

#if PRODUCER < CONSUMER
#error "the producer size must be not less than the consumer size"
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
    for (uint64_t i = 0; i < CONSUMER; i++) {
        char character;
        while (serial_dequeue(&queue_handle, &character) != 0);
        assert(character == (char)i);
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
