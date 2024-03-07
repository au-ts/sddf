/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sddf/util/fence.h>

#define I2C_MAX_DATA_SIZE 512
#define NUM_QUEUE_ENTRIES 512

#define RESPONSE_ERR 0
#define RESPONSE_ERR_TOKEN 1
/* Start of payload bytes in response data */
#define RESPONSE_DATA_OFFSET 2

#define I2C_ERR_OK 0
#define I2C_ERR_TIMEOUT 1
#define I2C_ERR_NACK 2
#define I2C_ERR_NOREAD 3

typedef uint8_t i2c_token_t;

enum i2c_token {
	/* END: Terminator for token list, has no meaning to hardware otherwise */
    I2C_TOKEN_END = 0x0,
	/* START: Begin a transfer. Causes master device to capture bus. */
    I2C_TOKEN_START = 0x1,
    /* ADDRESS WRITE: Used to wake up the target device on the bus.
	 * Sets up and following DATA tokens to be writes. */
    I2C_TOKEN_ADDR_WRITE = 0x2,
	/* ADDRESS READ: Same as ADDRW but sets up DATA tokens as reads. */
    I2C_TOKEN_ADDR_READ = 0x3,
	/* DATA_LAST: Used for read transactions to write a NACK to alert
	 * the slave device that the read is now over. */
    I2C_TOKEN_DATA_END = 0x4,
    /* STOP: Used to send the STOP condition on the bus to end a transaction.
     * Causes master to release the bus. */
    I2C_TOKEN_STOP = 0x5,
    /* Read or write one byte - the byte after this is treated as payload. */
    I2C_TOKEN_DATA = 0x6,
};

typedef struct queue_entry {
    /* Offset into the data region for where to look for the request data or
     * where to put the response data */
    size_t offset;
    /* Size of request/response data */
    unsigned int len;
    /* I2C bus address to operate on */
    size_t bus_address;
} i2c_queue_entry_t;

/* Circular buffer containing descriptors */
typedef struct i2c_queue {
    uint32_t tail;
    uint32_t head;
    i2c_queue_entry_t entries[NUM_QUEUE_ENTRIES];
} i2c_queue_t;

/* A ring handle for enqueing/dequeuing into  */
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
i2c_queue_handle_t i2c_queue_init(i2c_queue_t *request, i2c_queue_t *response);

/**
 * Check if the queue is empty.
 *
 * @param queue queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int i2c_queue_empty(i2c_queue_t *queue)
{
    return !((queue->tail - queue->head) % NUM_QUEUE_ENTRIES);
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
    return !((queue->tail - queue->head + 1) % NUM_QUEUE_ENTRIES);
}

static inline uint32_t i2c_queue_size(i2c_queue_t *queue)
{
    return (queue->tail - queue->head);
}

/**
 * Enqueue an element to the queue
 *
 * @param queue to enqueue into
 * @param bus_address bus address on the I2C device to request/response is for
 * @param offset offset in data region where the request data is or the response data will be
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
 * @return -1 when ring is empty, 0 on success.
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
 * Enqueue an element into a free ring buffer.
 * This indicates the buffer address parameter is currently free for re-use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int i2c_enqueue_request(i2c_queue_handle_t h, size_t bus_address, size_t offset, unsigned int len)
{
    return i2c_enqueue(h.request, bus_address, offset, len);
}

/**
 * Enqueue an element into a used ring buffer.
 * This indicates the buffer address parameter is currently in use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param len length of data inside the buffer above.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int i2c_enqueue_response(i2c_queue_handle_t h, size_t bus_address, size_t offset, unsigned int len)
{
    return i2c_enqueue(h.response, bus_address, offset, len);
}

/**
 * Dequeue an element from the free ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int i2c_dequeue_request(i2c_queue_handle_t h, size_t *bus_address, size_t *offset, unsigned int *len)
{
    return i2c_dequeue(h.request, bus_address, offset, len);
}

/**
 * Dequeue an element from a used ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int i2c_dequeue_response(i2c_queue_handle_t h, size_t *bus_address, size_t *offset, unsigned int *len)
{
    return i2c_dequeue(h.response, bus_address, offset, len);
}
