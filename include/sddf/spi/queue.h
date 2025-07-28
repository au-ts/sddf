/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sddf/util/fence.h>
#include <sddf/util/string.h>

//TODO
#define NUM_QUEUE_ENTRIES (128)
#define SPI_CS_MAX (16)

typedef enum spi_err {
    SPI_ERR_OK,
    SPI_ERR_OOB,
    SPI_ERR_UNALIGNED_OFFSET,
    SPI_ERR_PARTIAL_OVERLAP,
    SPI_ERR_UNTERM_TX,
    SPI_ERR_TIMEOUT,
    SPI_ERR_OTHER, // can be used for driver specific implementations
} spi_err_t;

static inline char *err_to_str(spi_err_t err) {
    switch (err) {
    case SPI_ERR_OK: return "SPI_ERR_OK";
    case SPI_ERR_OOB: return "SPI_ERR_OOB";
    case SPI_ERR_UNALIGNED_OFFSET: return "SPI_ERR_UNALIGNED_OFFSET";
    case SPI_ERR_PARTIAL_OVERLAP: return "SPI_ERR_PARTIAL_OVERLAP";
    case SPI_ERR_UNTERM_TX: return "SPI_ERR_UNTERM_TX";
    case SPI_ERR_TIMEOUT: return "SPI_ERR_TIMEOUT";
    case SPI_ERR_OTHER: return "SPI_ERR_OTHER";
    default: return "NOT_AN_SPI_ERROR";
    }
}

typedef struct spi_queue_ctrl {
    uint32_t tail, head;
} spi_queue_ctrl_t;

/* The two regions should overlap completely or be disjoint */
typedef struct spi_cmd {
    size_t read_offset;
    size_t write_offset;
    uint16_t len;
    bool cs_active_after_cmd;
} spi_cmd_t;

typedef struct spi_resp{
    spi_err_t err;
    uint16_t err_cmd_idx;
} spi_resp_t;

typedef uint8_t spi_cs_t;

typedef struct spi_cmd_queue {
    spi_queue_ctrl_t ctrl;
    bool updated;
    spi_cmd_t cmd[];
} spi_cmd_queue_t;

typedef struct spi_resp_queue {
    spi_queue_ctrl_t ctrl;
    spi_resp_t resp[];
} spi_resp_queue_t;

typedef struct spi_cs_queue {
    spi_queue_ctrl_t ctrl;
    spi_cs_t cs[];
} spi_cs_queue_t;


// TODO
#define CMD_LEN(len) (len ? len : UINT16_MAX + 1)


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
 * @return true indicates the queue is full, false otherwise.
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
 * Enqueue an element into the command queue
 *
 * @param queue queue to enqueue into.
 * @param read_offset offset into the data region to start reading from
 * @param write_offset offset into the data region to start writing from
 * @param len number of bytes to read/write, number of dummy cycles if no operation specified
 * @param cs_active_after_cmd should the CS remain low after this command?
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int spi_enqueue_cmd(spi_cmd_queue_t *queue, uint64_t read_offset, 
    uint64_t write_offset, uint16_t len, bool cs_active_after_cmd)
{
    if (spi_queue_full(queue->ctrl)) {
        return -1;
    }

    uint64_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
    queue->cmd[index].read_offset = read_offset;
    queue->cmd[index].write_offset = write_offset;
    queue->cmd[index].len = len;
    queue->cmd[index].cs_active_after_cmd = cs_active_after_cmd;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail++;

    return 0;
}

static inline int spi_mass_enqueue_cmd(spi_cmd_queue_t *queue, spi_cmd_t *cmds, uint32_t num_cmds) {
    if (num_cmds > NUM_QUEUE_ENTRIES - spi_queue_length(queue->ctrl)) {
        return -1;
    }

    for (uint32_t i = 0; i < num_cmds; i++) {
        uint64_t index = (queue->ctrl.tail + i) % NUM_QUEUE_ENTRIES;
        sddf_memcpy(&queue->cmd[index], &cmds[i], sizeof(spi_cmd_t));
    }

    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail += num_cmds;

    return 0;
}

/**
 * Enqueue an element into the response queue
 *
 * @param queue queue to enqueue into.
 * @param err error code encountered (or ERR_OK for no error)
 * @param err_cmd_idx index of command in failing command chian
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int spi_enqueue_resp(spi_resp_queue_t *queue, spi_err_t err, uint8_t err_cmd_idx)
{
    if (spi_queue_full(queue->ctrl)) {
        return -1;
    }

    uint64_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
    queue->resp[index].err_cmd_idx = err_cmd_idx;
    queue->resp[index].err = err;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail++;

    return 0;
}

/**
 * Enqueue a CS into the CS queue
 *
 * @param queue queue to enqueue into.
 * @param cs the chip select to enqueue
 *
 * @return -1 when queue is full, 0 on success.
 */
static inline int spi_enqueue_cs(spi_cs_queue_t *queue, spi_cs_t cs) 
{
    if (spi_queue_full(queue->ctrl)) {
        return -1;
    }

    uint64_t index = queue->ctrl.tail % NUM_QUEUE_ENTRIES;
    queue->cs[index] = cs;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.tail++;

    return 0;
}

/**
 * Dequeue an element from the request queue
 *
 * @param queue queue handle to dequeue from
 * TODO
 * @param len pointer for where to store the number of commands in the dequeued request
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int spi_dequeue_cmd(spi_cmd_queue_t *queue, size_t *read_offset, size_t *write_offset,
    uint16_t *len, bool *cs_active_after_cmd)
{
    if (spi_queue_empty(queue->ctrl)) {
        return -1;
    }

    uint64_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *read_offset = queue->cmd[index].read_offset;
    *write_offset = queue->cmd[index].write_offset;
    *len = queue->cmd[index].len;
    *cs_active_after_cmd = queue->cmd[index].cs_active_after_cmd;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}

/*
 * Dequeue an element from the response queue
 *
 * @param queue queue to dequeue from
 * @param err_cmd_idx index of the failing command
 * @param error error code encountered (or ERR_OK for no error)
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int spi_dequeue_resp(spi_resp_queue_t *queue, spi_err_t *err, uint16_t *err_cmd_idx)
{
    if (spi_queue_empty(queue->ctrl)) {
        return -1;
    }

    uint64_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *err = queue->resp[index].err;
    *err_cmd_idx = queue->resp[index].err_cmd_idx;

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}

/*
 * Dequeue an element from the cs queue
 *
 * @param queue queue handle to dequeue from
 * @param cs pointer to where to dequeue the CS
 *
 * @return -1 when queue is empty, 0 on success.
 */
static inline int spi_dequeue_cs(spi_cs_queue_t *queue, spi_cs_t *cs)
{
    if (spi_queue_empty(queue->ctrl)) {
        return -1;
    }

    uint64_t index = queue->ctrl.head % NUM_QUEUE_ENTRIES;
    *cs = queue->cs[index];

    THREAD_MEMORY_RELEASE();
    queue->ctrl.head++;

    return 0;
}
