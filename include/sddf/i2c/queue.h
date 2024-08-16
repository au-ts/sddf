/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sddf/util/fence.h>

/*
 * Here we choose the default data size and queue entries. This means
 * that by default the data region would need 4KiB of space (1 page on
 * AArch64 for example). These defaults have worked for our example systems
 * but are left configurable for the system designer if they are too small.
 */
#ifndef I2C_MAX_DATA_SIZE
#define I2C_MAX_DATA_SIZE 128
#endif

#ifndef NUM_QUEUE_ENTRIES
#define NUM_QUEUE_ENTRIES 32
#endif

#define RESPONSE_ERR 0
#define RESPONSE_ERR_TOKEN 1
/* Start of payload bytes in response data (index of first non error byte that driver adds) */
#define RESPONSE_DATA_OFFSET 2

#define I2C_ERR_OK 0
#define I2C_ERR_TIMEOUT 1
#define I2C_ERR_NACK 2
#define I2C_ERR_NOREAD 3
#define I2C_ERR_OTHER 3 // can be used for driver specific implementations

typedef uint8_t i2c_token_t;

enum i2c_token {
    /* END: Terminator for token list, has no meaning to hardware otherwise */
    I2C_TOKEN_END = 0x0,
    /* START: Begin a transfer. Causes master device to capture bus. */
    I2C_TOKEN_START = 0x1,
    /* ADDRESS WRITE: Used to wake up the target device on the bus.
     * The byte immediately following this token is an integer (N) length of the succeeding
       write. Max 256 (1**8). The next N bytes are the payload. */
    I2C_TOKEN_ADDR_WRITE = 0x2,
    /* ADDRESS READ: Same as ADDRW but sets up DATA tokens as reads.
       FIXME: N bytes must be padded after read to suit current transport layer. This should
              be replaced, ideally by using a separate shared buffer for return data*/
    I2C_TOKEN_ADDR_READ = 0x3,
    /* STOP: Used to send the STOP condition on the bus to end a transaction.
     * Causes master to release the bus. */
    I2C_TOKEN_STOP = 0x4,
};

typedef struct i2c_queue_entry {
    /* Offset into the data region for where to look for the request data or
     * where to put the response data */
    size_t offset;
    /* Size of request/response data */
    unsigned int len;
    /* I2C bus address to operate on */
    size_t bus_address;
} i2c_queue_entry_t;

/* Shared queue structure that contains either requests or responses */
typedef struct i2c_queue {
    uint32_t tail;
    uint32_t head;
    i2c_queue_entry_t entries[NUM_QUEUE_ENTRIES];
} i2c_queue_t;

/* Convenience struct for storing request and response queues */
typedef struct i2c_queue_handle {
    i2c_queue_t *request;
    i2c_queue_t *response;
} i2c_queue_handle_t;

/**
 * Initialise the queue.
 * Note that this assumes that the request and response queues are zero-initalised.
 *
 * @param queue queue handle to use.
 * @param request pointer to request queue in shared memory.
 * @param response pointer to response queue in shared memory.
 */
static inline i2c_queue_handle_t i2c_queue_init(i2c_queue_t *request, i2c_queue_t *response)
{
    i2c_queue_handle_t handle;
    handle.request = request;
    handle.response = response;

    return handle;
}

/**
 * Check if the queue is empty.
 *
 * @param queue queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int i2c_queue_empty(i2c_queue_t *queue)
{
    return queue->tail - queue->head == 0;
}

/**
 * Check if the queue is full
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int i2c_queue_full(i2c_queue_t *queue)
{
    return queue->tail - queue->head + 1 == NUM_QUEUE_ENTRIES;
}

/**
 * Get the number of entries in a queue
 *
 * @param queue queue to check.
 *
 * @return number of entries in a queue
 */
static inline uint32_t i2c_queue_length(i2c_queue_t *queue)
{
    return (queue->tail - queue->head);
}

/**
 * Enqueue an element to the queue
 *
 * @param queue to enqueue into
 * @param bus_address bus address on the I2C device that the request/response is for
 * @param offset offset into the data region where the request data is or the response data will be
 * @param len length of data at the offset given
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int i2c_enqueue(i2c_queue_t *queue, size_t bus_address, size_t offset, unsigned int len)
{
    if (i2c_queue_full(queue)) {
        return -1;
    }

    size_t index = queue->tail % NUM_QUEUE_ENTRIES;
    queue->entries[index].bus_address = bus_address;
    queue->entries[index].offset = offset;
    queue->entries[index].len = len;

    THREAD_MEMORY_RELEASE();
    queue->tail++;

    return 0;
}

/**
 * Dequeue an element from the queue
 *
 * @param queue queue to dequeue from
 * @param bus_address pointer for where to store the bus address associated with the dequeued entry
 * @param offset pointer for where to store teh offset of the data of associated with the dequeued entry
 * @param len pointer for where to store the length of data associated with the dequeued entry
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int i2c_dequeue(i2c_queue_t *queue, size_t *bus_address, size_t *offset, unsigned int *len)
{
    if (i2c_queue_empty(queue)) {
        return -1;
    }

    size_t index = queue->head % NUM_QUEUE_ENTRIES;
    *bus_address = queue->entries[index].bus_address;
    *offset = queue->entries[index].offset;
    *len = queue->entries[index].len;

    THREAD_MEMORY_RELEASE();
    queue->head++;

    return 0;
}

/**
 * Enqueue an element into the request queue
 *
 * @param queue queue handle to enqueue into.
 * @param bus_address bus address on the I2C device to request on
 * @param offset offset into the data region where the request data is
 * @param len length of data at the offset given
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int i2c_enqueue_request(i2c_queue_handle_t h, size_t bus_address, size_t offset, unsigned int len)
{
    return i2c_enqueue(h.request, bus_address, offset, len);
}

/**
 * Enqueue an element into the response queue
 *
 * @param queue queue handle to enqueue into.
 * @param bus_address bus address on the I2C device where the response came from
 * @param offset offset into the data region where the response data is
 * @param len length of data at the offset given
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int i2c_enqueue_response(i2c_queue_handle_t h, size_t bus_address, size_t offset, unsigned int len)
{
    return i2c_enqueue(h.response, bus_address, offset, len);
}

/**
 * Dequeue an element from the request queue
 *
 * @param queue queue handle to dequeue from
 * @param bus_address pointer for where to store the bus address associated with the dequeued request
 * @param offset pointer for where to store teh offset of the data of associated with the dequeued request
 * @param len pointer for where to store the length of data associated with the dequeued request
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int i2c_dequeue_request(i2c_queue_handle_t h, size_t *bus_address, size_t *offset, unsigned int *len)
{
    return i2c_dequeue(h.request, bus_address, offset, len);
}

/**
 * Dequeue an element from the response queue
 *
 * @param queue queue handle to dequeue from
 * @param bus_address pointer for where to store the bus address associated with the dequeued response
 * @param offset pointer for where to store teh offset of the data of associated with the dequeued response
 * @param len pointer for where to store the length of data associated with the dequeued response
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int i2c_dequeue_response(i2c_queue_handle_t h, size_t *bus_address, size_t *offset, unsigned int *len)
{
    return i2c_dequeue(h.response, bus_address, offset, len);
}
