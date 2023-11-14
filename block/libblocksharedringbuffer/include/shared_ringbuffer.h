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

/* Number of entries in shared ring buffer */
#define NUM_RING_ENTRIES 1024
/* Number of buffers the data region is configured to have. */
#define NUM_BUFFERS 2048
/* Size of a single buffer in the data region. Set to equal sector size. */
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
    response_status_t status; /* response status */
    void *cookie; /* index into client side metadata, @ericc: stores corresponding command ID */
    // @ericc: potentially return address and count on failure,
    // but I haven't found a case where a client needs 
    // to know that much information yet
    // uint16_t count /* on failure, the number of successfully transferred sectors */
    // void *encoded_addr /* on failure, the base dma address of contiguous buffers for transfer */
} response_t;

/* Circular buffer containing commands */
typedef struct cmd_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of entries in command ring buffer */
    bool notify_writer;
    bool notify_reader;
    bool plugged;
    command_t commands[NUM_RING_ENTRIES];
} cmd_ring_buffer_t;

/* Circular buffer containing responses */
typedef struct resp_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of entries in response ring buffer */
    bool notify_writer;
    bool notify_reader;
    response_t responses[NUM_RING_ENTRIES];
} resp_ring_buffer_t;

typedef struct data_region {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffer segments in shared data */
} data_region_t;

/* A ring handle for enqueing/dequeuing into  */
typedef struct ring_handle {
    cmd_ring_buffer_t *cmd_ring;
    resp_ring_buffer_t *resp_ring;
    data_region_t *data_region;
} ring_handle_t;

/**
 * Initialise the shared ring buffer.
 *
 * @param ring ring handle to use.
 * @param command pointer to command ring in shared memory.
 * @param response pointer to response ring in shared memory.
 * @param buffer_init 1 indicates the read and write indices in shared memory need to be initialised.
 *                    0 indicates they do not. Only one side of the shared memory regions needs to do this.
 * @param command_size number of entries in command ring.
 * @param response_size number of entries in response ring.
 * @param data_region_size number of buffer segments in shared data region.
 */
void ring_init(ring_handle_t *ring,
                cmd_ring_buffer_t *command,
                resp_ring_buffer_t *response,
                data_region_t *data_region,
                int buffer_init,
                uint32_t command_size,
                uint32_t response_size,
                uint32_t data_region_size);

/**
 * Check if the command ring buffer is empty.
 *
 * @param ring ring handle containing command ring buffer.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int cmd_ring_empty(ring_handle_t *ring)
{
    return !((ring->cmd_ring->write_idx - ring->cmd_ring->read_idx) % ring->cmd_ring->size);
}

/**
 * Check if the response ring buffer is empty.
 *
 * @param ring ring handle containing response ring buffer.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int resp_ring_empty(ring_handle_t *ring)
{
    return !((ring->resp_ring->write_idx - ring->resp_ring->read_idx) % ring->resp_ring->size);
}

// @ericc: we are leaving a gap of one buffer before we consider the ring full
/**
 * Check if the command ring buffer is full.
 *
 * @param ring ring handle containing command ring buffer.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int cmd_ring_full(ring_handle_t *ring)
{
    return !((ring->cmd_ring->write_idx - ring->cmd_ring->read_idx + 1) % ring->cmd_ring->size);
}

/**
 * Check if the response ring buffer is full.
 *
 * @param ring ring handle containing response ring buffer.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int resp_ring_full(ring_handle_t *ring)
{
    return !((ring->resp_ring->write_idx - ring->resp_ring->read_idx + 1) % ring->resp_ring->size);
}

/**
 * Check if the data region is full.
 *
 * @param ring ring handle containing data region.
 * @param count the number of contiguous buffers to be inserted.
 *
 * @return true indicates the buffer is full, false otherwise.
 */
static inline int data_region_full(ring_handle_t *ring, uint32_t count)
{
    return !((ring->data_region->write_idx - ring->data_region->read_idx + count + 1) % ring->data_region->size);
}

/**
 * Get the number of elements in a command ring buffer.
 *
 * @param ring ring handle containing command and response ring buffers.
 *
 * @return number of elements in the ring buffer.
 */
static inline int cmd_ring_size(ring_handle_t *ring)
{
    return (ring->cmd_ring->write_idx - ring->cmd_ring->read_idx);
}

/**
 * Get the number of elements in a response ring buffer.
 *
 * @param ring ring handle containing command and response ring buffers.
 *
 * @return number of elements in the ring buffer.
 */
static inline int resp_ring_size(ring_handle_t *ring)
{
    return (ring->resp_ring->write_idx - ring->resp_ring->read_idx);
}

// @ericc: maybe pass in a pointer to a struct instead? Lots of arguments here
/**
 * Enqueue an element into the command ring buffer.
 *
 * @param ring Ring handle containing command ring to enqueue to.
 * @param code command code.
 * @param base_addr base address of contiguous buffer(s) where command data is stored.
 * @param sector sector number to read/write.
 * @param count the number of contiguous buffers used by this command.
 * @param cookie command ID to identify this command.
 *
 * @return -1 when ring is full or data region is full, 0 on success.
 */
static inline int enqueue_cmd(ring_handle_t *ring,
                            command_code_t code,
                            uintptr_t base_addr,
                            uint32_t sector,
                            uint16_t count,
                            void *cookie)
{
    if (cmd_ring_full(ring) || data_region_full(ring, count)) {
        return -1;
    }

    ring->cmd_ring->commands[ring->cmd_ring->write_idx % ring->cmd_ring->size].code = code;
    ring->cmd_ring->commands[ring->cmd_ring->write_idx % ring->cmd_ring->size].encoded_base_addr = base_addr;
    ring->cmd_ring->commands[ring->cmd_ring->write_idx % ring->cmd_ring->size].sector = sector;
    ring->cmd_ring->commands[ring->cmd_ring->write_idx % ring->cmd_ring->size].count = count;
    ring->cmd_ring->commands[ring->cmd_ring->write_idx % ring->cmd_ring->size].cookie = cookie;

    THREAD_MEMORY_RELEASE();
    ring->cmd_ring->write_idx++;
    ring->data_region->write_idx += (uint32_t)count;

    return 0;
}

/**
 * Enqueue an element into a used ring buffer.
 * This indicates the command has been processed and a response is ready.
 *
 * @param ring Ring handle containing response ring to enqueue to.
 * @param status response status.
 * @param cookie command ID to identify which command the response is for.
 *
 * @return -1 when response ring is full, 0 on success.
 */
static inline int enqueue_resp(ring_handle_t *ring,
                                response_status_t status,
                                void *cookie)
{
    if (resp_ring_full(ring)) {
        return -1;
    }

    ring->resp_ring->responses[ring->resp_ring->write_idx % ring->resp_ring->size].status = status;
    ring->resp_ring->responses[ring->resp_ring->write_idx % ring->resp_ring->size].cookie = cookie;

    THREAD_MEMORY_RELEASE();
    ring->resp_ring->write_idx++;

    return 0;
}

/**
 * Dequeue an element from the command ring buffer.
 *
 * @param ring Ring handle containing command ring to dequeue from.
 * @param code pointer to variable to store command code.
 * @param base_addr pointer to the address of where to store base address of buffer(s) storing command data.
 * @param sector pointer to variable to store sector number to read/write.
 * @param count pointer to variable to store number of sectors to read/write.
 * @param cookie pointer to cookie to store command ID.
 *
 * @return -1 when command ring is empty, 0 on success.
 */
static inline int dequeue_cmd(ring_handle_t *ring,
                            command_code_t *code,
                            uintptr_t *base_addr,
                            uint32_t *sector,
                            uint16_t *count,
                            void **cookie)
{
    if (cmd_ring_empty(ring)) {
        return -1;
    }

    *code = ring->cmd_ring->commands[ring->cmd_ring->read_idx % ring->cmd_ring->size].code;
    *base_addr = ring->cmd_ring->commands[ring->cmd_ring->read_idx % ring->cmd_ring->size].encoded_base_addr;
    *sector = ring->cmd_ring->commands[ring->cmd_ring->read_idx % ring->cmd_ring->size].sector;
    *count = ring->cmd_ring->commands[ring->cmd_ring->read_idx % ring->cmd_ring->size].count;
    *cookie = ring->cmd_ring->commands[ring->cmd_ring->read_idx % ring->cmd_ring->size].cookie;

    THREAD_MEMORY_RELEASE();
    ring->cmd_ring->read_idx++;
    ring->data_region->read_idx += (uint32_t)*count;

    return 0;
}

/**
 * Dequeue an element from a response ring buffer.
 *
 * @param ring Ring handle containing response ring to dequeue from.
 * @param status pointer to the address of where to store response status.
 * @param cookie pointer to cookie storing command ID to idenfity which command this response is for.
 * @return -1 when response ring is empty, 0 on success.
 */
static inline int dequeue_resp(ring_handle_t *ring,
                                response_status_t *status,
                                void **cookie)
{
    if (resp_ring_empty(ring)) {
        return -1;
    }

    *status = ring->resp_ring->responses[ring->resp_ring->read_idx % ring->resp_ring->size].status;
    *cookie = ring->resp_ring->responses[ring->resp_ring->read_idx % ring->resp_ring->size].cookie;

    THREAD_MEMORY_RELEASE();
    ring->resp_ring->read_idx++;

    return 0;
}

/**
 * Set the plug of the command ring to true.
 *
 * @param ring Ring handle containing command ring to check for plug.
*/
static inline void cmd_ring_plug(ring_handle_t *ring) {
    ring->cmd_ring->plugged = true;
}

/**
 * Set the plug of the command ring to false.
 *
 * @param ring Ring handle containing command ring to check for plug.
*/
static inline void cmd_ring_unplug(ring_handle_t *ring) {
    ring->cmd_ring->plugged = false;
}

/**
 * Check the current value of the command ring plug.
 *
 * @param ring Ring handle containing command ring to check for plug.
 *
 * @return true when command ring is plugged, false when unplugged.
*/
static inline bool cmd_ring_plugged(ring_handle_t *ring) {
    return ring->cmd_ring->plugged;
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
