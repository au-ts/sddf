/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <sddf/util/fence.h>
#include <sddf/spi/config.h>

typedef enum spi_status {
    SPI_STATUS_OK = 0,
    SPI_STATUS_ERR_CMD_OOB = -1,
    SPI_STATUS_ERR_CMD_UNALIGNED_OFFSET = -2,
    SPI_STATUS_ERR_CMD_PARTIAL_OVERLAP = -3,
    SPI_STATUS_ERR_PARTIAL_TXN = -4,
    SPI_STATUS_ERR_TIMEOUT = -5,
    SPI_STATUS_ERR_CMD_QUEUE_FULL = -6,
    SPI_STATUS_ERR_RESP_QUEUE_EMPTY = -7,
    SPI_STATUS_ERR_OTHER = -256, // can be used for driver specific implementations
} spi_status_t;

static inline char *spi_status_str(spi_status_t status)
{
    switch (status) {
    case SPI_STATUS_OK:
        return "SPI_STATUS_OK";
    case SPI_STATUS_ERR_CMD_OOB:
        return "SPI_STATUS_ERR_CMD_OOB";
    case SPI_STATUS_ERR_CMD_UNALIGNED_OFFSET:
        return "SPI_STATUS_ERR_CMD_UNALIGNED_OFFSET";
    case SPI_STATUS_ERR_CMD_PARTIAL_OVERLAP:
        return "SPI_STATUS_ERR_CMD_PARTIAL_OVERLAP";
    case SPI_STATUS_ERR_PARTIAL_TXN:
        return "SPI_STATUS_ERR_PARTIAL_TXN";
    case SPI_STATUS_ERR_TIMEOUT:
        return "SPI_STATUS_ERR_TIMEOUT";
    case SPI_STATUS_ERR_OTHER:
        return "SPI_STATUS_ERR_OTHER";
    default:
        return "NOT_AN_SPI_STATUS";
    }
}

// As a command length of 0 does not make sense, it should be interpreted as the maximum size
// representable in that type plus 1
// i.e. shifting the domain of a uint8_t from [0, 65535] to [1, 65536]
#define CMD_LEN(len) (len ? len : UINT16_MAX + 1)

// The two regions, [read_offset, read_offset + len] and [write_offset, write_offset + len]
// should overlap completely or be disjoint
typedef struct spi_cmd {
    size_t read_offset;
    size_t write_offset;
    uint16_t len;
    bool cs_active_after_cmd;
} spi_cmd_t;

typedef struct spi_resp {
    spi_status_t status;
    uint16_t err_cmd_idx;
} spi_resp_t;

typedef uint8_t spi_cs_t;

typedef struct spi_cmd_queue {
    uint32_t head;
    uint32_t tail;
    spi_cmd_t element[];
} spi_cmd_queue_t;

typedef struct spi_resp_queue {
    uint32_t head;
    uint32_t tail;
    spi_resp_t element[];
} spi_resp_queue_t;

typedef struct spi_cmd_cs_queue {
    uint32_t head;
    uint32_t tail;
    spi_cs_t element[];
} spi_cmd_cs_queue_t;

typedef struct spi_resp_cs_queue {
    uint32_t head;
    uint32_t tail;
    spi_cs_t element[];
} spi_resp_cs_queue_t;

typedef struct spi_handle {
    spi_cmd_queue_t *spi_cmd_queue;
    spi_resp_queue_t *spi_resp_queue;
    spi_cmd_cs_queue_t *spi_cmd_cs_queue;
    spi_resp_cs_queue_t *spi_resp_cs_queue;
    uint8_t queue_capacity_bits;
} spi_handle_t;

/**
 * Initialise the shared queues
 *
 * @param handle queue handle to use
 * @param spi_cmd_queue pointer to cmd queue in shared memory
 * @param spi_resp_queue pointer to resp queue in shared memory
 * @param spi_cmd_cs_queue pointer to cmd_cs queue in shared memory
 * @param spi_resp_cs_queue pointer to resp_cs queue in shared memory
 * @param queue_capacity bits the queue capacity should be equal to 1 << queue_capacity_bits
 *
 * @return whether queue_capacity_bits is longer than the width of the queue index or not
 */
static inline bool spi_handle_init(spi_handle_t *handle, spi_cmd_queue_t *spi_cmd_queue,
                                   spi_resp_queue_t *spi_resp_queue, spi_cmd_cs_queue_t *spi_cmd_cs_queue,
                                   spi_resp_cs_queue_t *spi_resp_cs_queue, uint8_t queue_capacity_bits)
{
    if (queue_capacity_bits >= UINT32_WIDTH) {
        return false;
    }

    handle->spi_cmd_queue = spi_cmd_queue;
    handle->spi_resp_queue = spi_resp_queue;
    handle->spi_cmd_cs_queue = spi_cmd_cs_queue;
    handle->spi_resp_cs_queue = spi_resp_cs_queue;
    handle->queue_capacity_bits = queue_capacity_bits;

    return true;
}

/**
 * Check if the cmd queue is empty
 *
 * @param handle the queue handle to use
 *
 * @return whether the cmd queue is empty or not
 */
static inline bool spi_cmd_queue_empty(spi_handle_t *handle)
{
    spi_cmd_queue_t *queue = handle->spi_cmd_queue;
    return queue->head == queue->tail;
}

/**
 * Check if the cmd queue is full
 *
 * @param handle the queue handle to use
 *
 * @return whether the cmd queue is full or not
 */
static inline bool spi_cmd_queue_full(spi_handle_t *handle)
{
    spi_cmd_queue_t *queue = handle->spi_cmd_queue;
    return queue->tail - queue->head == 1 << handle->queue_capacity_bits;
}

/**
 * Get the number of elements in the cmd queue
 *
 * @param handle the queue handle to use
 *
 * @return number of elements in the queue
 */
static inline uint32_t spi_cmd_queue_len(spi_handle_t *handle)
{
    spi_cmd_queue_t *queue = handle->spi_cmd_queue;
    return queue->tail - queue->head;
}

/**
 * Enqueue an element into the cmd queue
 *
 * @param handle the queue handle to use
 * @param read_offset
 * @param write_offset
 * @param len
 * @param cs_active_after_cmd
 *
 * @return if the enqueue was successful
 */
static inline bool spi_enqueue_cmd(spi_handle_t *handle, size_t read_offset, size_t write_offset, uint16_t len,
                                   bool cs_active_after_cmd)
{
    if (spi_cmd_queue_full(handle)) {
        return false;
    }

    spi_cmd_queue_t *queue = handle->spi_cmd_queue;
    uint32_t index = queue->tail % (1 << handle->queue_capacity_bits);
    queue->element[index].read_offset = read_offset;
    queue->element[index].write_offset = write_offset;
    queue->element[index].len = len;
    queue->element[index].cs_active_after_cmd = cs_active_after_cmd;

    THREAD_MEMORY_RELEASE();
    queue->tail++;

    return true;
}

/**
 * Dequeue an element from the cmd queue
 *
 * @param handle the queue handle to use
 * @param read_offset
 * @param write_offset
 * @param len
 * @param cs_active_after_cmd
 *
 * @return if the dequeue was successful
 */
static inline bool spi_dequeue_cmd(spi_handle_t *handle, size_t *read_offset, size_t *write_offset, uint16_t *len,
                                   bool *cs_active_after_cmd)
{
    if (spi_cmd_queue_empty(handle)) {
        return false;
    }

    spi_cmd_queue_t *queue = handle->spi_cmd_queue;
    uint32_t index = queue->head % (1 << handle->queue_capacity_bits);
    *read_offset = queue->element[index].read_offset;
    *write_offset = queue->element[index].write_offset;
    *len = queue->element[index].len;
    *cs_active_after_cmd = queue->element[index].cs_active_after_cmd;

    THREAD_MEMORY_RELEASE();
    queue->head++;

    return true;
}

/**
 * Enqueue len elements into the cmd queue
 *
 * @param handle the queue handle to use
 * @param element pointer to a contiguous array of spi_cmd_t
 * @param len the amount of elements to enqueue
 *
 * @return if the enqueue was successful
 */
static inline bool spi_mass_enqueue_cmd(spi_handle_t *handle, spi_cmd_t *element, uint32_t len)
{
    if (len + spi_cmd_queue_len(handle) > 1 << handle->queue_capacity_bits) {
        return false;
    }

    spi_cmd_queue_t *queue = handle->spi_cmd_queue;
    for (uint32_t i = 0; i < len; i++) {
        uint32_t index = (queue->tail + i) % (1 << handle->queue_capacity_bits);
        memcpy(&queue->element[index], &element[i], sizeof(spi_cmd_t));
    }

    THREAD_MEMORY_RELEASE();
    queue->tail += len;

    return true;
}

/**
 * Check if the resp queue is empty
 *
 * @param handle the queue handle to use
 *
 * @return whether the resp queue is empty or not
 */
static inline bool spi_resp_queue_empty(spi_handle_t *handle)
{
    spi_resp_queue_t *queue = handle->spi_resp_queue;
    return queue->head == queue->tail;
}

/**
 * Check if the resp queue is full
 *
 * @param handle the queue handle to use
 *
 * @return whether the resp queue is full or not
 */
static inline bool spi_resp_queue_full(spi_handle_t *handle)
{
    spi_resp_queue_t *queue = handle->spi_resp_queue;
    return queue->tail - queue->head == 1 << handle->queue_capacity_bits;
}

/**
 * Get the number of elements in the resp queue
 *
 * @param handle the queue handle to use
 *
 * @return number of elements in the queue
 */
static inline uint32_t spi_resp_queue_len(spi_handle_t *handle)
{
    spi_resp_queue_t *queue = handle->spi_resp_queue;
    return queue->tail - queue->head;
}

/**
 * Enqueue an element into the resp queue
 *
 * @param handle the queue handle to use
 * @param status
 * @param err_cmd_idx
 *
 * @return if the enqueue was successful
 */
static inline bool spi_enqueue_resp(spi_handle_t *handle, spi_status_t status, uint16_t err_cmd_idx)
{
    if (spi_resp_queue_full(handle)) {
        return false;
    }

    spi_resp_queue_t *queue = handle->spi_resp_queue;
    uint32_t index = queue->tail % (1 << handle->queue_capacity_bits);
    queue->element[index].status = status;
    queue->element[index].err_cmd_idx = err_cmd_idx;

    THREAD_MEMORY_RELEASE();
    queue->tail++;

    return true;
}

/**
 * Dequeue an element from the resp queue
 *
 * @param handle the queue handle to use
 * @param status
 * @param err_cmd_idx
 *
 * @return if the dequeue was successful
 */
static inline bool spi_dequeue_resp(spi_handle_t *handle, spi_status_t *status, uint16_t *err_cmd_idx)
{
    if (spi_resp_queue_empty(handle)) {
        return false;
    }

    spi_resp_queue_t *queue = handle->spi_resp_queue;
    uint32_t index = queue->head % (1 << handle->queue_capacity_bits);
    *status = queue->element[index].status;
    *err_cmd_idx = queue->element[index].err_cmd_idx;

    THREAD_MEMORY_RELEASE();
    queue->head++;

    return true;
}

/**
 * Enqueue len elements into the resp queue
 *
 * @param handle the queue handle to use
 * @param element pointer to a contiguous array of spi_resp_t
 * @param len the amount of elements to enqueue
 *
 * @return if the enqueue was successful
 */
static inline bool spi_mass_enqueue_resp(spi_handle_t *handle, spi_resp_t *element, uint32_t len)
{
    if (len + spi_resp_queue_len(handle) > 1 << handle->queue_capacity_bits) {
        return false;
    }

    spi_resp_queue_t *queue = handle->spi_resp_queue;
    for (uint32_t i = 0; i < len; i++) {
        uint32_t index = (queue->tail + i) % (1 << handle->queue_capacity_bits);
        memcpy(&queue->element[index], &element[i], sizeof(spi_resp_t));
    }

    THREAD_MEMORY_RELEASE();
    queue->tail += len;

    return true;
}

/**
 * Check if the cmd_cs queue is empty
 *
 * @param handle the queue handle to use
 *
 * @return whether the cmd_cs queue is empty or not
 */
static inline bool spi_cmd_cs_queue_empty(spi_handle_t *handle)
{
    spi_cmd_cs_queue_t *queue = handle->spi_cmd_cs_queue;
    return queue->head == queue->tail;
}

/**
 * Check if the cmd_cs queue is full
 *
 * @param handle the queue handle to use
 *
 * @return whether the cmd_cs queue is full or not
 */
static inline bool spi_cmd_cs_queue_full(spi_handle_t *handle)
{
    spi_cmd_cs_queue_t *queue = handle->spi_cmd_cs_queue;
    return queue->tail - queue->head == 1 << handle->queue_capacity_bits;
}

/**
 * Get the number of elements in the cmd_cs queue
 *
 * @param handle the queue handle to use
 *
 * @return number of elements in the queue
 */
static inline uint32_t spi_cmd_cs_queue_len(spi_handle_t *handle)
{
    spi_cmd_cs_queue_t *queue = handle->spi_cmd_cs_queue;
    return queue->tail - queue->head;
}

/**
 * Enqueue an element into the cmd_cs queue
 *
 * @param handle the queue handle to use
 * @param cs
 *
 * @return if the enqueue was successful
 */
static inline bool spi_enqueue_cmd_cs(spi_handle_t *handle, spi_cs_t cs)
{
    if (spi_cmd_cs_queue_full(handle)) {
        return false;
    }

    spi_cmd_cs_queue_t *queue = handle->spi_cmd_cs_queue;
    uint32_t index = queue->tail % (1 << handle->queue_capacity_bits);
    queue->element[index] = cs;

    THREAD_MEMORY_RELEASE();
    queue->tail++;

    return true;
}

/**
 * Dequeue an element from the cmd_cs queue
 *
 * @param handle the queue handle to use
 * @param cs
 *
 * @return if the dequeue was successful
 */
static inline bool spi_dequeue_cmd_cs(spi_handle_t *handle, spi_cs_t *cs)
{
    if (spi_cmd_cs_queue_empty(handle)) {
        return false;
    }

    spi_cmd_cs_queue_t *queue = handle->spi_cmd_cs_queue;
    uint32_t index = queue->head % (1 << handle->queue_capacity_bits);
    *cs = queue->element[index];

    THREAD_MEMORY_RELEASE();
    queue->head++;

    return true;
}

/**
 * Enqueue len elements into the cmd_cs queue
 *
 * @param handle the queue handle to use
 * @param element pointer to a contiguous array of spi_cmd_cs_t
 * @param len the amount of elements to enqueue
 *
 * @return if the enqueue was successful
 */
static inline bool spi_mass_enqueue_cmd_cs(spi_handle_t *handle, spi_cs_t *element, uint32_t len)
{
    if (len + spi_cmd_cs_queue_len(handle) > 1 << handle->queue_capacity_bits) {
        return false;
    }

    spi_cmd_cs_queue_t *queue = handle->spi_cmd_cs_queue;
    for (uint32_t i = 0; i < len; i++) {
        uint32_t index = (queue->tail + i) % (1 << handle->queue_capacity_bits);
        memcpy(&queue->element[index], &element[i], sizeof(spi_cs_t));
    }

    THREAD_MEMORY_RELEASE();
    queue->tail += len;

    return true;
}

/**
 * Check if the resp_cs queue is empty
 *
 * @param handle the queue handle to use
 *
 * @return whether the resp_cs queue is empty or not
 */
static inline bool spi_resp_cs_queue_empty(spi_handle_t *handle)
{
    spi_resp_cs_queue_t *queue = handle->spi_resp_cs_queue;
    return queue->head == queue->tail;
}

/**
 * Check if the resp_cs queue is full
 *
 * @param handle the queue handle to use
 *
 * @return whether the resp_cs queue is full or not
 */
static inline bool spi_resp_cs_queue_full(spi_handle_t *handle)
{
    spi_resp_cs_queue_t *queue = handle->spi_resp_cs_queue;
    return queue->tail - queue->head == 1 << handle->queue_capacity_bits;
}

/**
 * Get the number of elements in the resp_cs queue
 *
 * @param handle the queue handle to use
 *
 * @return number of elements in the queue
 */
static inline uint32_t spi_resp_cs_queue_len(spi_handle_t *handle)
{
    spi_resp_cs_queue_t *queue = handle->spi_resp_cs_queue;
    return queue->tail - queue->head;
}

/**
 * Enqueue an element into the resp_cs queue
 *
 * @param handle the queue handle to use
 * @param cs
 *
 * @return if the enqueue was successful
 */
static inline bool spi_enqueue_resp_cs(spi_handle_t *handle, spi_cs_t cs)
{
    if (spi_resp_cs_queue_full(handle)) {
        return false;
    }

    spi_resp_cs_queue_t *queue = handle->spi_resp_cs_queue;
    uint32_t index = queue->tail % (1 << handle->queue_capacity_bits);
    queue->element[index] = cs;

    THREAD_MEMORY_RELEASE();
    queue->tail++;

    return true;
}

/**
 * Dequeue an element from the resp_cs queue
 *
 * @param handle the queue handle to use
 * @param cs
 *
 * @return if the dequeue was successful
 */
static inline bool spi_dequeue_resp_cs(spi_handle_t *handle, spi_cs_t *cs)
{
    if (spi_resp_cs_queue_empty(handle)) {
        return false;
    }

    spi_resp_cs_queue_t *queue = handle->spi_resp_cs_queue;
    uint32_t index = queue->head % (1 << handle->queue_capacity_bits);
    *cs = queue->element[index];

    THREAD_MEMORY_RELEASE();
    queue->head++;

    return true;
}

/**
 * Enqueue len elements into the resp_cs queue
 *
 * @param handle the queue handle to use
 * @param element pointer to a contiguous array of spi_resp_cs_t
 * @param len the amount of elements to enqueue
 *
 * @return if the enqueue was successful
 */
static inline bool spi_mass_enqueue_resp_cs(spi_handle_t *handle, spi_cs_t *element, uint32_t len)
{
    if (len + spi_resp_cs_queue_len(handle) > 1 << handle->queue_capacity_bits) {
        return false;
    }

    spi_resp_cs_queue_t *queue = handle->spi_resp_cs_queue;
    for (uint32_t i = 0; i < len; i++) {
        uint32_t index = (queue->tail + i) % (1 << handle->queue_capacity_bits);
        memcpy(&queue->element[index], &element[i], sizeof(spi_cs_t));
    }

    THREAD_MEMORY_RELEASE();
    queue->tail += len;

    return true;
}
