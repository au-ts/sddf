/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <microkit.h>
// #include "util/include/util.h"
#include "util/include/fence.h"

/* Number of buffers each ring is configured to have. */
#define NUM_BUFFERS 2048
/* Size of a single buffer storing command data. Set to equal sector size. */
#define BUFFER_SIZE 512

/* Command code for block */
typedef enum command_code {
    BLK_COMMAND_READ,
    BLK_COMMAND_WRITE,
    BLK_COMMAND_BARRIER,
} command_code_t;

/* Response status for block */
typedef enum response_status {
    BLK_RESPONSE_OK,
    BLK_RESPONSE_ERROR,
} response_status_t;

/* */
typedef struct command {
    command_code_t code; /* command code */
    uintptr_t encoded_base_addr; /* the encoded dma base address of the first buffer in a set of contiguous buffers storing command data */
    uint32_t sector; /* sector number to read/write */
    uint16_t count; /* number of sectors to read/write, also indicates the number of buffers used by this command when buf_size == sector_size */
    void *cookie; /* index into client side metadata, @ericc: stores command ID */
} command_t;

/* */
typedef struct response {
    response_status_t status; /* response code */
    // @ericc: potentially return address and count on failure,
    // but I haven't found a case where a client needs 
    // to know that much information yet
    // uint16_t count /* on failure, the number of successfully transferred sectors */
    // void *encoded_addr /* on failure, the base dma address for transfer */
    void *cookie; /* index into client side metadata, @ericc: stores corresponding command ID */
} response_t;

/* Circular buffer containing commands */
typedef struct cmd_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size;
    uint32_t buf_size;
    bool notify_writer;
    bool notify_reader;
    bool plugged;
    command_t buffers[NUM_BUFFERS];
} cmd_ring_buffer_t;

/* Circular buffer containing responses */
typedef struct resp_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size;
    bool notify_writer;
    bool notify_reader;
    response_t buffers[NUM_BUFFERS];
} resp_ring_buffer_t;

/* A ring handle for enqueing/dequeuing into  */
typedef struct ring_handle {
    cmd_ring_buffer_t *cmd_ring;
    resp_ring_buffer_t *resp_ring;
} ring_handle_t;

/**
 * Initialise the shared ring buffer.
 *
 * @param ring ring handle to use.
 * @param free pointer to free ring in shared memory.
 * @param used pointer to 'used' ring in shared memory.
 * @param buffer_init 1 indicates the read and write indices in shared memory need to be initialised.
 *                    0 inidicates they do not. Only one side of the shared memory regions needs to do this.
 */
void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, int buffer_init, uint32_t free_size, uint32_t used_size);
// TODO: change this cmd & resp instead of free & used

/**
 * Check if the command ring buffer is empty.
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int cmd_ring_empty(cmd_ring_buffer_t *ring)
{
    return !((ring->write_idx - ring->read_idx) % ring->size);
}

/**
 * Check if the response ring buffer is empty.
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int resp_ring_empty(resp_ring_buffer_t *ring)
{
    return !((ring->write_idx - ring->read_idx) % ring->size);
}

/**
 * Check if the command ring buffer is full
 *
 * @param ring ring buffer to check.
 * @param count the number of contiguous buffers to be inserted
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int cmd_ring_full(cmd_ring_buffer_t *ring, uint16_t count)
{
    return !((ring->write_idx - ring->read_idx + count) % ring->size);
}

/**
 * Check if the response ring buffer is full
 *
 * @param ring ring buffer to check.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int resp_ring_full(resp_ring_buffer_t *ring)
{
    return !((ring->write_idx - ring->read_idx + 1) % ring->size);
}

/**
 * Get the number of elements in a command ring buffer.
 *
 * @param ring ring buffer to check.
 *
 * @return number of elements in the ring buffer.
 */
static inline int cmd_ring_size(cmd_ring_buffer_t *ring)
{
    return (ring->write_idx - ring->read_idx);
}

static inline int resp_ring_size(resp_ring_buffer_t *ring)
{
    return (ring->write_idx - ring->read_idx);
}

// @ericc: maybe pass in a pointer to a struct instead? Lots of arguments here
/**
 * Enqueue an element into a command ring buffer.
 * This indicates the set of contiguous buffer(s) with base address parameter that is currently in use by a command
 *
 * @param ring ring handle to enqueue command into.
 * @param base_addr base address of contiguous buffer(s) shared memory where data is stored.
 * @param count the number of contiguous buffers used by this command.
 * @param cookie command ID to be retrieved on dequeueing.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue_cmd(ring_handle_t *ring,
                            command_code_t code,
                            uintptr_t base_addr,
                            uint32_t sector,
                            uint16_t count,
                            void *cookie)
{
    if (cmd_ring_full(ring->cmd_ring, count)) {
        return -1;
    }

    for (int i = 0; i < count; i++) {
        ring->cmd_ring->buffers[ring->cmd_ring->write_idx % ring->cmd_ring->size].code = code;
        ring->cmd_ring->buffers[ring->cmd_ring->write_idx % ring->cmd_ring->size].encoded_base_addr = base_addr + i;
        ring->cmd_ring->buffers[ring->cmd_ring->write_idx % ring->cmd_ring->size].sector = sector;
        ring->cmd_ring->buffers[ring->cmd_ring->write_idx % ring->cmd_ring->size].count = count;
        ring->cmd_ring->buffers[ring->cmd_ring->write_idx % ring->cmd_ring->size].cookie = cookie;

        THREAD_MEMORY_RELEASE();
        ring->cmd_ring->write_idx++;
    }

    return 0;
}

/**
 * Enqueue an element into a used ring buffer.
 * This indicates the buffer address parameter is currently in use.
 *
 * @param ring Ring handle to enqueue into.
 * @param buffer address into shared memory where data is stored.
 * @param cookie optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is full, 0 on success.
 */
static inline int enqueue_resp(ring_handle_t *ring, void *cookie)
{
    if (resp_ring_full(ring->resp_ring)) {
        return -1;
    }

    ring->resp_ring->buffers[ring->resp_ring->write_idx % ring->resp_ring->size].cookie = cookie;
}

/**
 * Dequeue an element from the free ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_cmd(ring_handle_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return dequeue(ring->free_ring, addr, len, cookie);
}

/**
 * Dequeue an element from a used ring buffer.
 *
 * @param ring Ring handle to dequeue from.
 * @param buffer pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer optional pointer to data required on dequeueing.
 *
 * @return -1 when ring is empty, 0 on success.
 */
static inline int dequeue_resp(ring_handle_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return dequeue(ring->used_ring, addr, len, cookie);
}

/**
 * Set the plug of a ring to true.
 *
 * @param ring Ring handle to plug.
*/
static inline void ring_plug(ring_buffer_t *ring) {
    ring->plugged = true;
}

/**
 * Set the plug of a ring to false.
 *
 * @param ring Ring handle to unplug.
*/
static inline void ring_unplug(ring_buffer_t *ring) {
    ring->plugged = false;
}


/**
 * Check the current value of the plug.
 *
 * @param ring Ring handle to check plug.
 *
 * @return true when ring is plugged, false when unplugged.
*/
static inline bool ring_plugged(ring_buffer_t *ring) {
    return ring->plugged;
}

// @ericc: need to refactor, currently unused.
/**
 * Dequeue an element from a ring buffer.
 * This function is intended for use by the driver, to collect a pointer
 * into this structure to be passed around as a cookie.
 *
 * @param ring Ring buffer to dequeue from.
 * @param addr pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer to store a pointer to this particular entry.
 *
 * @return -1 when ring is empty, 0 on success.
 */
// static int driver_dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
// {
//     if (ring_empty(ring)) {
//         return -1;
//     }

//     *addr = ring->buffers[ring->read_idx % ring->size].encoded_addr;
//     *len = ring->buffers[ring->read_idx % ring->size].len;
//     *cookie = &ring->buffers[ring->read_idx % ring->size];

//     THREAD_MEMORY_RELEASE();
//     ring->read_idx++;

//     return 0;
// }
