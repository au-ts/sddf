/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <stdlib.h>
#include <pthread.h>

#include <sddf/network/queue.h>

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

net_queue_handle_t queue;

void *producer(void *p)
{
    for (uint64_t i = 0; i < PRODUCER; i++) {
        net_buff_desc_t desc = { 0 };
        desc.io_or_offset = i;
        while (net_enqueue_free(&queue, desc) != 0);
    }
    return NULL;
}

void *consumer(void *p)
{
    for (uint64_t i = 0; i < CONSUMER; i++) {
        net_buff_desc_t desc;
        while (net_dequeue_free(&queue, &desc) != 0);
        assert(desc.io_or_offset == i);
    }
    return NULL;
}

int main()
{
    net_queue_t * free_queue = malloc(sizeof(net_queue_t) + sizeof(net_buff_desc_t) * QUEUE_SIZE);
    if (free_queue == NULL) {
        exit(1);
    }
    free_queue->head = 0;
    free_queue->tail = 0;
    free_queue->consumer_signalled = 0;

    net_queue_t * active_queue = malloc(sizeof(net_queue_t) + sizeof(net_buff_desc_t) * QUEUE_SIZE);
    if (active_queue == NULL) {
        exit(1);
    }
    active_queue->head = 0;
    active_queue->tail = 0;
    active_queue->consumer_signalled = 0;

    net_queue_init(&queue, free_queue, active_queue, QUEUE_SIZE);

    pthread_t t1, t2;
    if (pthread_create(&t1, NULL, producer, NULL) != 0) {
        exit(1);
    }
    if (pthread_create(&t2, NULL, consumer, NULL) != 0) {
        exit(1);
    }

    pthread_join(t2, NULL);
    pthread_join(t1, NULL);

    free(active_queue);
    free(free_queue);

    return 0;
}
