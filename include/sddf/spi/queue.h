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
 * that by default the control region would need 4KiB of space (1 page on
 * AArch64 for example). These defaults have worked for our example systems
 * but are left configurable for the system designer if they are too small.
 */
// TODO: where is this even used?
#ifndef SPI_MAX_DATA_SIZE
#define SPI_MAX_DATA_SIZE 128
#endif

#ifndef NUM_QUEUE_ENTRIES
// TODO: bodgetopia up here; context - fit queue into 1 pg lol
//#define NUM_QUEUE_ENTRIES 32
#define NUM_QUEUE_ENTRIES 4
#endif

// TODO: finish 
typedef enum spi_err {
    SPI_ERR_OK,
    SPI_ERR_TIMEOUT,
    SPI_ERR_INVALID_CS_LINE,
    SPI_ERR_OOB,
    SPI_ERR_INVALID_CMD,
    SPI_ERR_OTHER, // can be used for driver specific implementations
} spi_err_t;

// Pattern for continuous query and response, offset by a cmd
// WRITE -> TRANSFER -> ... -> READ
//
// Pattern for programming some stuff
// WRITE -> ...
//
// Pattern for QSPI
// WRITE (inst) -> WRITE (addr) -> DUMMY -> ... -> READ (byte 0) -> 
// READ (byte 1) -> ...
typedef enum spi_cmd_mode {
    SPI_READ,
    SPI_WRITE,
    SPI_TRANSFER,
    SPI_DUMMY, // TODO: remove since no QSPI support?
    NUM_MODES
} spi_cmd_mode_t;

typedef uint8_t spi_cs_line_t;

typedef struct spi_cmd {
    /* offset into buffer region */
    size_t read_offset;
    size_t write_offset;
    /* length of the referenced buffer */
    uint16_t len;
    /* what command do? */
    spi_cmd_mode_t mode; 
} spi_cmd_t;

/* A queue entry is a single logical transaction. The offset points to a list of len spi_cmd_t's */
typedef struct spi_queue_request {
    // NOTE: control and buffer base are set by the virtualiser, not the client. We use the same struct
    // for symmetry, and to avoid a copy.
    
    /* These two vaddrs are unfortunately needed because it complicates verification to just let
     * the driver access this from SDFgen. We arguably should just trust SDFgen to avoid this.*/
    /* Pointer to first command used in control region for this request*/
    uintptr_t control_start_vaddr;
    /* Start of buffer region, pointed to by cmds in the control region */
    uintptr_t buffer_base_addr;
    /* Number of commands in list. Max 32 per transaction */
    uint8_t len;
    /* SPI cs line to operate on */
    spi_cs_line_t cs_line;
} spi_queue_request_t; // Packed as written -> 16 bytes

typedef struct spi_queue_ctrl {
    uint32_t tail, head;
} spi_queue_ctrl_t;

/* Request queue. */ 
typedef struct spi_request_queue {
    spi_queue_ctrl_t ctrl;
    spi_queue_request_t requests[NUM_QUEUE_ENTRIES];
} spi_request_queue_t;

typedef struct spi_queue_response {
    /* Index of command causing error */
    uint8_t err_cmd;
    spi_cs_line_t cs_line;
    spi_err_t error;
} spi_queue_response_t; // Packed as written -> 16 bytes

/* Response queue. Client already knows where all data is, so this is just a mechanism for
 * error reporting. */
typedef struct spi_response_queue {
    spi_queue_ctrl_t ctrl;
    spi_queue_response_t responses[NUM_QUEUE_ENTRIES];
} spi_response_queue_t;

/* Convenience struct for storing request and response queues */
typedef struct spi_queue_handle {
    spi_request_queue_t *request;
    spi_response_queue_t *response;
} spi_queue_handle_t;

/**
 * Initialise the queue.
 * Note that this assumes that the request and response queues are zero-initalised.
 *
 * @param queue queue handle to use.
 * @param request pointer to request queue in shared memory.
 * @param response pointer to response queue in shared memory.
 */
static inline spi_queue_handle_t spi_queue_init(spi_request_queue_t *request, spi_response_queue_t *response)
{
    spi_queue_handle_t handle;
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
static inline int spi_queue_empty(spi_queue_ctrl_t q_ctrl)
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
static inline int spi_queue_full(spi_queue_ctrl_t q_ctrl)
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
static inline uint32_t spi_queue_length(spi_queue_ctrl_t q_ctrl)
{
    return (q_ctrl.tail - q_ctrl.head);
}

/**
 * Enqueue an element into the request queue
 *
 * @param queue queue handle to enqueue into.
 * @param cs_line bus address on the SPI device to request on
 * @param control_start_vaddr pointer to command in control region
 * @param buffer_base_addr pointer to start of buffer region for this command. Set by virt.
 * @param len length of buffer at the offset given
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int spi_enqueue_request(spi_queue_handle_t h, spi_cs_line_t cs_line,
                                      uintptr_t control_start_vaddr, uintptr_t buffer_base_addr, uint8_t len)
{
    spi_request_queue_t *queue = h.request;
    if (spi_queue_full(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
    queue->requests[index].cs_line = cs_line;
    queue->requests[index].control_start_vaddr = control_start_vaddr;
    queue->requests[index].buffer_base_addr = buffer_base_addr;
    queue->requests[index].len = len;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail++;

    return 0;
}

/**
 * Enqueue an element into the response queue
 *
 * @param queue queue handle to enqueue into.
 * @param cs_line bus address on the SPI device where the response came from
 * @param error error code encountered (or ERR_OK for no error)
 * @param err_cmd index of command in failing command chian
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int spi_enqueue_response(spi_queue_handle_t h, spi_cs_line_t cs_line, spi_err_t error,
                                       uint16_t err_cmd)
{
    spi_response_queue_t *queue = h.response;
    if (spi_queue_full(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
    queue->responses[index].cs_line = cs_line;
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
 * @param cs_line pointer for where to store the bus address associated with the dequeued request
 * @param control_start_vaddr pointer to command in control region
 * @param buffer_base_addr pointer to start of buffer region for this command. Set by virt.
 * @param len pointer for where to store the length of the buffer associated with the dequeued request
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int spi_dequeue_request(spi_queue_handle_t h, spi_cs_line_t *cs_line, uintptr_t *control_start_vaddr,
                                      uintptr_t *buffer_base_addr, uint16_t *len)
{
    spi_request_queue_t *queue = h.request;
    if (spi_queue_empty(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *cs_line = queue->requests[index].cs_line;
    *control_start_vaddr = queue->requests[index].control_start_vaddr;
    *buffer_base_addr = queue->requests[index].buffer_base_addr;
    *len = queue->requests[index].len;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}

/**
 * Dequeue an element from the response queue
 *
 * @param queue queue handle to dequeue from
 * @param cs_line pointer for where to store the bus address associated with the dequeued response
 * @param offset pointer for where to store the offset of the buffer associated with the dequeued response
 * @param len pointer for where to store the length of the buffer associated with the dequeued response
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int spi_dequeue_response(spi_queue_handle_t h, spi_cs_line_t *cs_line, spi_err_t *error,
                                       size_t *err_cmd)
{
    spi_response_queue_t *queue = h.response;
    if (spi_queue_empty(queue->ctrl)) {
        return -1;
    }

    size_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *cs_line = queue->responses[index].cs_line;
    *error= queue->responses[index].error;
    *err_cmd = queue->responses[index].err_cmd;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}
