/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>

/*
 * The data region contains buffers for the driver to read from / write to. This macro is used
 * to ensure offsets are appropriately contained within the region as expected.
 * TODO: probably delete this? this serves no obvious purpose with sdfgen parsing such information.
 */
#ifndef I2C_MAX_DATA_SIZE
#define I2C_MAX_DATA_SIZE 256
#endif

/*
 * We define the (default) queue size to fill an entire 4KiB page in the queue region.
 * NOTE: we size this based on the request queue as it contains larger structs and there
 * should never be more responses than requests.
 *
 * sizeof(i2c_cmd_t) = (8 + 1 + 1) + 2 padding = 16 bytes.
 * Queue size = 4096 // 16 = 256 (before considering bookkeeping struct)
 */
#ifndef I2C_QUEUE_CAPACITY
#define QUEUE_HANDLE_SZ (32)    // 24 bytes + padding
#define I2C_QUEUE_CAPACITY ((4096 - QUEUE_HANDLE_SZ) / sizeof(i2c_cmd_t))
#endif

typedef enum i2c_err {
    I2C_ERR_OK,
    I2C_ERR_MALFORMED_TRANSACTION,
    I2C_ERR_MALFORMED_HEADER,
    I2C_ERR_UNPERMITTED_ADDR,
    I2C_ERR_TIMEOUT,
    I2C_ERR_NACK,
    I2C_ERR_NOREAD,
    I2C_ERR_BADSEQ,
    I2C_ERR_OTHER, // can be used for driver specific implementations
} i2c_err_t;

/* This isn't a command but instead designates a command header */
#define I2C_FLAG_HEAD (1 << 0)
/* This is a read command. */
#define I2C_FLAG_READ (1 << 1)
/*
 * This is a write-read op. I.e. we write the index of a register
 * in the device before we read. Special case, as we never can
 * intermingle data otherwise.
 * ALWAYS implies a read.
 */
#define I2C_FLAG_WRRD (1 << 2)
/* We want a stop at the end of the command. */
#define I2C_FLAG_STOP (1 << 3)
/* This is a continuation of a previous command,
 * demarcating a repeated start condition. CAUTION: must match read/write
 * direction of last op! */
#define I2C_FLAG_RSTART (1 << 4)
typedef uint8_t i2c_cmd_flags_t;
typedef uint8_t i2c_addr_t; // We currently only support the 7 bit addressing mode.

typedef struct i2c_cmd {
    union {
        /* Location of read destination / write data in data region */
        /* If a writeread operation, assumed that first byte of buffer contains sub address of byte register */
        uint8_t *data;

        /* Fields for header members */
        struct {
            uint16_t batch_len;
            i2c_addr_t address;
        } i2c_header;
    } payload;
    /* Size of read/write operation. Max 256 back-to-back reads / 64KiB write */
    /* Unused if this is a header command */
    uint8_t data_len;
    i2c_cmd_flags_t flag_mask;
} i2c_cmd_t;

typedef struct i2c_queue_ctrl {
    uint32_t tail, head;
} i2c_queue_ctrl_t;

/* Request queue. Master-mode I2C is inherently asymmetrical and responses can be very simple. */
typedef struct i2c_request_queue {
    // Producers for the active queue must batch update the tail
    // to prevent a race condition between the clients and virt.
    uint32_t staged_active_tail;
    i2c_queue_ctrl_t ctrl;
    i2c_cmd_t cmds[I2C_QUEUE_CAPACITY];
} i2c_request_queue_t;

typedef struct i2c_response {
    /* Index of command causing error */
    size_t err_cmd;
    i2c_addr_t bus_address;
    i2c_err_t error;
} i2c_response_t; // Packed as written -> 16 bytes

/* Response queue. Client already knows where all data is, so this is just a mechanism for
 * error reporting. */
typedef struct i2c_response_queue {
    i2c_queue_ctrl_t ctrl;
    i2c_response_t responses[I2C_QUEUE_CAPACITY];
} i2c_response_queue_t;

/* Convenience struct for storing request and response queues */
typedef struct i2c_queue_handle {
    i2c_request_queue_t *request;
    i2c_response_queue_t *response;
} i2c_queue_handle_t;

/**
 * Parse an i2c command to check if it is a header. If it is a header, return batch
 * length, otherwise return 0. Return -1 if header is invalid.
 *
 * @param i2c_cmd_t to inspect.
 * @returns int: positive batch size, 0 for not a command, negative for invalid command
 */
static inline int i2c_parse_cmd_header(i2c_cmd_t *cmd)
{
    if (cmd->flag_mask & I2C_FLAG_HEAD) {
        // Sanity: we error out if other flags are set. This is just to prevent user
        // confusion as the other flags are irrelevant if this is a header.
        if (cmd->flag_mask != I2C_FLAG_HEAD)
            return -1;

        // Batches must contain something.
        if (cmd->payload.i2c_header.batch_len != 0) {
            return cmd->payload.i2c_header.batch_len;
        }
        return -1;
    }
    return 0;
}

/**
 * Initialise the queue.
 * Note that this assumes that the request and response queues are zero-initalised.
 *
 * @param queue queue handle to use.
 * @param request pointer to request queue in shared memory.
 * @param response pointer to response queue in shared memory.
 */
static inline i2c_queue_handle_t i2c_queue_init(i2c_request_queue_t *request, i2c_response_queue_t *response)
{
    i2c_queue_handle_t handle;
    handle.request = request;
    handle.response = response;
    handle.request->staged_active_tail = 0;

    return handle;
}

/**
 * Check if the queue is empty by looking at all committed
 * entries.
 *
 * @param queue queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int i2c_queue_empty(i2c_queue_ctrl_t q_ctrl)
{
    return q_ctrl.tail == q_ctrl.head;
}

/**
 * Check if the queue is full by looking at all commited entries.
 * Use i2c_request_queue_full() to consider uncommitted entries.
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int i2c_queue_full(i2c_queue_ctrl_t q_ctrl)
{
    return q_ctrl.tail - q_ctrl.head + 1 == I2C_QUEUE_CAPACITY;
}

/**
 * Check if the active request queue of a queue handle is full, considering
 * uncommitted entries. This function should only be called by a producer of the queue!
 *
 * @param h queue handle queue to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int i2c_request_queue_full(i2c_queue_handle_t h)
{
    return (h.request->staged_active_tail - h.request->ctrl.head + 1) == I2C_QUEUE_CAPACITY;
}

/**
 * Get the number of entries in a queue.
 * This does not consider uncommitted entries. Use i2c_request_queue_length() to
 * consider unstaged requests.
 *
 * @param queue queue to check.
 *
 * @return number of entries in a queue
 */
static inline uint32_t i2c_queue_length(i2c_queue_ctrl_t q_ctrl)
{
    return (q_ctrl.tail - q_ctrl.head);
}

/**
 * Get the number of entries in the request queue of a handle, considering all
 * unstaged entries. This should only be used by the producer of the queue request
 * queue.
 *
 * @param h queue handle to check.
 *
 * @return number of entries in a queue
 */
static inline uint32_t i2c_request_queue_length(i2c_queue_handle_t h)
{
    return (h.request->staged_active_tail - h.request->ctrl.head);
}

/**
 * Enqueue an element into the request queue but do not commit it.
 * Use i2c_request_commit() to batch update the queue with all uncommitted
 * requests.
 *
 * @param queue queue handle to enqueue into.
 * @param cmd command to enqueue.
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int i2c_enqueue_request(i2c_queue_handle_t h, i2c_cmd_t cmd)
{
    i2c_request_queue_t *queue = h.request;
    if (i2c_request_queue_full(h)) {
        return -1;
    }
    // If the staged tail is less than the real tail, queue is broken.
    assert(queue->staged_active_tail >= queue->ctrl.tail);

    size_t index = queue->staged_active_tail % I2C_QUEUE_CAPACITY;
    queue->cmds[index] = cmd;
    // We update the staged tail instead of the real one.
    queue->staged_active_tail++;

    return 0;
}

/**
 *  Commit a series of outstanding enqueues to the queue handle. This will cause
 *  enqueued entries to become visible to the consumer.
 *  @param h queue handle to commit.
 */
static inline void i2c_request_commit(i2c_queue_handle_t h)
{
    i2c_request_queue_t *queue = h.request;
    // If the staged tail is less than the real tail, queue is broken.
    assert(queue->staged_active_tail >= queue->ctrl.tail);
    // Do commit
    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail = queue->staged_active_tail;
}

/**
 * Discard all outstanding enqueues by resetting the staged tail.
 * @param h queue handle to abort.
 */
static inline void i2c_request_abort(i2c_queue_handle_t h)
{
    i2c_request_queue_t *queue = h.request;
    queue->staged_active_tail = queue->ctrl.tail;
}

/**
 * Enqueue an element into the response queue
 *
 * @param queue queue handle to enqueue into.
 * @param bus_address bus address on the I2C device where the response came from
 * @param error error code encountered (or ERR_OK for no error)
 * @param err_cmd index of command in failing command chian
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int i2c_enqueue_response(i2c_queue_handle_t h, i2c_addr_t bus_address, i2c_err_t error, size_t err_cmd)
{
    i2c_response_queue_t *queue = h.response;
    if (i2c_queue_full(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.tail % I2C_QUEUE_CAPACITY;
    queue->responses[index].bus_address = bus_address;
    queue->responses[index].error = error;
    queue->responses[index].err_cmd = err_cmd;
    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail++;
    return 0;
}

/**
 * Dequeue an element from the request queue
 *
 * @param queue queue handle to dequeue from.
 * @param cmd location to dequeue command into.
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int i2c_dequeue_request(i2c_queue_handle_t h, i2c_cmd_t *cmd)
{
    i2c_request_queue_t *queue = h.request;
    if (i2c_queue_empty(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.head % I2C_QUEUE_CAPACITY;
    *cmd = queue->cmds[index];
    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
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
static inline int i2c_dequeue_response(i2c_queue_handle_t h, i2c_addr_t *bus_address, i2c_err_t *error, size_t *err_cmd)
{
    i2c_response_queue_t *queue = h.response;
    if (i2c_queue_empty(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.head % I2C_QUEUE_CAPACITY;
    *bus_address = queue->responses[index].bus_address;
    *error = queue->responses[index].error;
    *err_cmd = queue->responses[index].err_cmd;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}
