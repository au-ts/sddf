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

typedef enum i2c_err {
    I2C_ERR_OK,
    I2C_ERR_TIMEOUT,
    I2C_ERR_NACK,
    I2C_ERR_NOREAD,
    I2C_ERR_BADSEQ,
    I2C_ERR_OTHER, // can be used for driver specific implementations
} i2c_err_t;

#define I2C_FLAG_READ (1)   // This is a read command.
#define I2C_FLAG_WRRD (2) // This is a write-read op. I.e. we write the index of a register                                              \
                            // in the device before we read. Speciali case, as we never can                                                \
                            // intermingle data otherwise.
#define I2C_FLAG_STOP (4) // We want a stop at the end of the command.
#define I2C_FLAG_RSTART (8) // This is a continuation of a previous command, demarcating a                                                 \
                            // repeated start condition. CAUTION: must match read/write                                                    \
                            // direction of last op!
typedef uint8_t i2c_cmd_flags_t;
typedef uint8_t i2c_addr_t; // We currently only support the 7 bit addressing mode.

typedef struct i2c_cmd {
    /* Location of read destination / write data in meta region */
    /* If a writeread operation, assumed that first byte of buffer contains sub address of byte register */
    size_t offset;
    /* Size of read/write operation. Max 256 back-to-back reads / 64KiB write */
    uint8_t len;
    i2c_cmd_flags_t flag_mask;
} i2c_cmd_t;

/* A queue entry is a single logical transaction. The offset points to a list of len i2c_cmd_t's */
typedef struct i2c_queue_request {
    // NOTE: data and meta base are set by the virtualiser, not the client. We use the same struct
    // for symmetry, and to avoid a copy.

    /* These two vaddrs are unfortunately needed because it complicates verification to just let
     * the driver access this from SDFgen. We arguably should just trust SDFgen to avoid this.*/
    /* Pointer to first command used in data region for this request*/
    uintptr_t data_start_vaddr;
    /* Start of meta region, pointed to by cmds in the data region */
    uintptr_t meta_base_vaddr;
    /* Number of commands in list. Max 32 per transaction */
    uint8_t len;
    /* I2C bus address to operate on */
    i2c_addr_t bus_address;
} i2c_queue_request_t; // Packed as written -> 16 bytes

typedef struct i2c_queue_ctrl {
    uint32_t tail, head;
} i2c_queue_ctrl_t;

/* Request queue. Master-mode I2C is inherently asymmetrical and responses can be very simple. */
typedef struct i2c_request_queue {
    i2c_queue_ctrl_t ctrl;
    i2c_queue_request_t requests[NUM_QUEUE_ENTRIES];
} i2c_request_queue_t;

typedef struct i2c_queue_response {
    /* Index of command causing error */
    uint8_t err_cmd;
    i2c_addr_t bus_address;
    i2c_err_t error;
} i2c_queue_response_t; // Packed as written -> 16 bytes

/* Response queue. Client already knows where all data is, so this is just a mechanism for
 * error reporting. */
typedef struct i2c_response_queue {
    i2c_queue_ctrl_t ctrl;
    i2c_queue_response_t responses[NUM_QUEUE_ENTRIES];
} i2c_response_queue_t;

/* Convenience struct for storing request and response queues */
typedef struct i2c_queue_handle {
    i2c_request_queue_t *request;
    i2c_response_queue_t *response;
} i2c_queue_handle_t;

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

    return handle;
}

/**
 * Check if the queue is empty.
 *
 * @param queue queue to check.
 *
 * @return true indicates the queue is empty, false otherwise.
 */
static inline int i2c_queue_empty(i2c_queue_ctrl_t q_ctrl)
{
    return q_ctrl.tail - q_ctrl.head == 0;
}

/**
 * Check if the queue is full
 *
 * @param queue queue to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int i2c_queue_full(i2c_queue_ctrl_t q_ctrl)
{
    return q_ctrl.tail - q_ctrl.head + 1 == NUM_QUEUE_ENTRIES;
}

/**
 * Get the number of entries in a queue
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
 * Enqueue an element into the request queue
 *
 * @param queue queue handle to enqueue into.
 * @param bus_address bus address on the I2C device to request on
 * @param data_start_vaddr pointer to command in data region
 * @param meta_base_vaddr pointer to start of meta region for this command. Set by virt.
 * @param len length of data at the offset given
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int i2c_enqueue_request(i2c_queue_handle_t h, i2c_addr_t bus_address, uintptr_t data_start_vaddr,
                                      uintptr_t meta_base_vaddr, uint8_t len)
{
    i2c_request_queue_t *queue = h.request;
    if (i2c_queue_full(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
    queue->requests[index].bus_address = bus_address;
    queue->requests[index].data_start_vaddr = data_start_vaddr;
    queue->requests[index].meta_base_vaddr = meta_base_vaddr;
    queue->requests[index].len = len;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail++;

    return 0;
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
static inline int i2c_enqueue_response(i2c_queue_handle_t h, i2c_addr_t bus_address, i2c_err_t error, uint16_t err_cmd)
{
    i2c_response_queue_t *queue = h.response;
    if (i2c_queue_full(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
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
 * @param queue queue handle to dequeue from
 * @param bus_address pointer for where to store the bus address associated with the dequeued request
 * @param data_start_vaddr pointer to command in data region
 * @param meta_base_vaddr pointer to start of meta region for this command. Set by virt.
 * @param len pointer for where to store the length of data associated with the dequeued request
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int i2c_dequeue_request(i2c_queue_handle_t h, i2c_addr_t *bus_address, uintptr_t *data_start_vaddr,
                                      uintptr_t *meta_base_vaddr, uint16_t *len)
{
    i2c_request_queue_t *queue = h.request;
    if (i2c_queue_empty(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *bus_address = queue->requests[index].bus_address;
    *data_start_vaddr = queue->requests[index].data_start_vaddr;
    *meta_base_vaddr = queue->requests[index].meta_base_vaddr;
    *len = queue->requests[index].len;

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

    size_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *bus_address = queue->responses[index].bus_address;
    *error = queue->responses[index].error;
    *err_cmd = queue->responses[index].err_cmd;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}
