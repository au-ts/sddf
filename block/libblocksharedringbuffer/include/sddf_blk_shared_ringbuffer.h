/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
// #include "util/include/util.h"
#include "util/include/fence.h"

/* Number of buffers the command ring is configured to have. */
#define SDDF_BLK_NUM_CMD_BUFFERS 1024
/* Number of buffers the response ring is configured to have. */
#define SDDF_BLK_NUM_RESP_BUFFERS 1024
/* Number of buffers the data region is configured to have. */
#define SDDF_BLK_NUM_DATA_BUFFERS 4096
/* Size of a single data buffer. Set to equal sector size. */
#define SDDF_BLK_DATA_BUFFER_SIZE 512

/* Number of bits in an element of available bitmap */
#define SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE 32
/* Size of available bitmap */
#define SDDF_BLK_AVAIL_BITMAP_SIZE (SDDF_BLK_NUM_DATA_BUFFERS / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE)

/* Command code for block */
typedef enum sddf_blk_command_code {
    SDDF_BLK_COMMAND_READ,
    SDDF_BLK_COMMAND_WRITE,
    SDDF_BLK_COMMAND_FLUSH,
    SDDF_BLK_COMMAND_BARRIER,
} sddf_blk_command_code_t;

/* Response status for block */
typedef enum sddf_blk_response_status {
    SDDF_BLK_RESPONSE_OK,
    SDDF_BLK_RESPONSE_ERROR,
} sddf_blk_response_status_t;

/* Command struct contained in command ring */
typedef struct sddf_blk_command {
    sddf_blk_command_code_t code; /* command code */
    uintptr_t addr; /*  */
    uint32_t sector; /* sector number to read/write */
    uint16_t count; /* number of sectors to read/write, also indicates the length of descriptor chain due to buf_size == sector_size */
    uint32_t id; /* stores command ID */
} sddf_blk_command_t;

/* Response struct contained in response ring */
typedef struct sddf_blk_response {
    sddf_blk_response_status_t status; /* response status */
    uintptr_t addr; /* encoded dma address of data */
    uint16_t count; /* number of sectors allocated for corresponding command */
    uint16_t successful_count; /* number of sectors successfully read/written */
    uint32_t id; /* stores corresponding command ID */
} sddf_blk_response_t;

/* Circular buffer containing commands */
typedef struct sddf_blk_cmd_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffers in command ring buffer */
    bool plugged; /* prevent commands from being dequeued when plugged */
    sddf_blk_command_t buffers[SDDF_BLK_NUM_CMD_BUFFERS];
} sddf_blk_cmd_ring_buffer_t;

/* Circular buffer containing responses */
typedef struct sddf_blk_resp_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffers in response ring buffer */
    sddf_blk_response_t buffers[SDDF_BLK_NUM_RESP_BUFFERS];
} sddf_blk_resp_ring_buffer_t;

/* Data struct that handles allocation and freeing of data buffers */
typedef struct sddf_blk_data {
    uint32_t avail_bitpos; /* bit position of next avail buffer */
    uint32_t avail_bitmap[SDDF_BLK_AVAIL_BITMAP_SIZE]; /* Bit map representing avail data buffers */
    uint32_t num_buffers; /* number of buffers in data region */
    uintptr_t addr; /* encoded base address of data region */
} sddf_blk_data_t;

/* A ring handle for queueing/dequeueing command and responses */
typedef struct sddf_blk_ring_handle {
    sddf_blk_cmd_ring_buffer_t *cmd_ring;
    sddf_blk_resp_ring_buffer_t *resp_ring;
    sddf_blk_data_t *data;
} sddf_blk_ring_handle_t;

/**
 * Initialise the shared ring buffer.
 *
 * @param ring_handle ring handle to use.
 * @param command pointer to command ring in shared memory.
 * @param response pointer to response ring in shared memory.
 * @param data pointer to data region metadata in shared memory.
 * @param buffer_init 1 indicates the read and write indices in shared memory need to be initialised.
 *                    0 indicates they do not. Only one side of the shared memory regions needs to do this.
 * @param command_size number of buffers in command ring.
 * @param response_size number of buffers in response ring.
 * @param data_addr encoded base address of data region.
 * @param data_num_buffers number of buffers in data region.
 */
void sddf_blk_ring_init(sddf_blk_ring_handle_t *ring_handle,
                        sddf_blk_cmd_ring_buffer_t *command,
                        sddf_blk_resp_ring_buffer_t *response,
                        sddf_blk_data_t *data,
                        int buffer_init,
                        uint32_t command_size,
                        uint32_t response_size,
                        uintptr_t data_addr,
                        uint32_t data_num_buffers);

/**
 * Check if the command ring buffer is empty.
 *
 * @param ring_handle ring handle containing command ring buffer.
 *
 * @return true indicates the buffer is empty, false otherwise.
 */
static inline int sddf_blk_cmd_ring_empty(sddf_blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->cmd_ring->write_idx - ring_handle->cmd_ring->read_idx) % ring_handle->cmd_ring->size);
}

/**
 * Check if the response ring buffer is empty.
 *
 * @param ring_handle ring handle containing response ring buffer.
 *
 * @return true indicates the response ring buffer is empty, false otherwise.
 */
static inline int sddf_blk_resp_ring_empty(sddf_blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->resp_ring->write_idx - ring_handle->resp_ring->read_idx) % ring_handle->resp_ring->size);
}

// @ericc: this leaves a gap of one buffer before we consider the ring full
/**
 * Check if the command ring buffer is full.
 *
 * @param ring_handle ring handle containing command ring buffer.
 *
 * @return true indicates the command ring buffer is full, false otherwise.
 */
static inline int sddf_blk_cmd_ring_full(sddf_blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->cmd_ring->write_idx - ring_handle->cmd_ring->read_idx + 1) % ring_handle->cmd_ring->size);
}

/**
 * Check if the response ring buffer is full.
 *
 * @param ring_handle ring handle containing response ring buffer.
 *
 * @return true indicates the response ring buffer is full, false otherwise.
 */
static inline int sddf_blk_resp_ring_full(sddf_blk_ring_handle_t *ring_handle)
{
    return !((ring_handle->resp_ring->write_idx - ring_handle->resp_ring->read_idx + 1) % ring_handle->resp_ring->size);
}

/**
 * Get the number of elements in a command ring buffer.
 *
 * @param ring_handle ring handle containing command and response ring buffers.
 *
 * @return number of elements in the ring buffer.
 */
static inline int sddf_blk_cmd_ring_size(sddf_blk_ring_handle_t *ring_handle)
{
    return (ring_handle->cmd_ring->write_idx - ring_handle->cmd_ring->read_idx);
}

/**
 * Get the number of elements in a response ring buffer.
 *
 * @param ring_handle ring handle containing command and response ring buffers.
 *
 * @return number of elements in the ring buffer.
 */
static inline int sddf_blk_resp_ring_size(sddf_blk_ring_handle_t *ring_handle)
{
    return (ring_handle->resp_ring->write_idx - ring_handle->resp_ring->read_idx);
}

/**
 * Check if count is higher than the number of buffers until end of data region.
 * When this is true requesting count number of free buffers will overflow the data region.
 *
 * @param ring_handle ring handle containing data region.
 * @param count number of buffers to check.
 *
 * @return true indicates the data region will overflow, false otherwise.
 */
static inline int sddf_blk_data_end(sddf_blk_ring_handle_t *ring_handle, uint16_t count)
{
    return (sddf_blk_data_endcount(ring_handle) < count);
}

/**
 * Get the number of buffers until the end of the data region.
 *
 * @param ring_handle ring handle containing data region.
 * 
 * @return number of buffers until the end of the data region.
 */
static inline uint32_t sddf_blk_data_endcount(sddf_blk_ring_handle_t *ring_handle)
{
    return ring_handle->data->num_buffers - ring_handle->data->avail_bitpos;
}

/**
 * Check if the data region has count number of free buffers.
 *
 * @param ring_handle ring handle containing data region.
 * @param count number of buffers to check.
 *
 * @return true indicates the data region has count number of free buffers, false otherwise.
 */
int sddf_blk_data_full(sddf_blk_ring_handle_t *ring_handle, uint16_t count);

/**
 * Get count many free buffers in the data region.
 *
 * @param ring_handle ring handle containing data region.
 * @param addr pointer to base address of the resulting contiguous buffer.
 * @param count number of free buffers to get.
 *
 * @return -1 when data region is full, -2 when data region overflows the end, 0 on success.
 */
int sddf_blk_data_get_buffer(sddf_blk_ring_handle_t *ring_handle, uintptr_t *addr, uint16_t count);

/**
 * Free count many available buffers in the data region.
 *
 * @param ring_handle ring handle containing data region.
 * @param addr base address of the contiguous buffer to free.
 * @param count number of buffers to free.
 * 
 * @return -1 when data region overflows the end, 0 on success
 */
int sddf_blk_data_free_buffer(sddf_blk_ring_handle_t *ring_handle, uintptr_t addr, uint16_t count);

/**
 * Enqueue an element into the command ring buffer.
 *
 * @param ring_handle Ring handle containing command ring to enqueue to.
 * @param code command code.
 * @param addr encoded dma address of data to read/write.
 * @param sector sector number to read/write.
 * @param count the number of sectors to read/write
 * @param id command ID to identify this command.
 *
 * @return -1 when command ring is full, 0 on success.
 */
static inline int sddf_blk_enqueue_cmd(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_command_code_t code,
                                        uintptr_t addr,
                                        uint32_t sector,
                                        uint16_t count,
                                        uint32_t id)
{
    if (sddf_blk_cmd_ring_full(ring_handle)) {
        return -1;
    }

    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].code = code;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].addr = addr;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].sector = sector;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].count = count;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].id = id;

    THREAD_MEMORY_RELEASE();
    ring_handle->cmd_ring->write_idx++;

    return 0;
}

/**
 * Enqueue an element into the response ring buffer.
 * This indicates the command has been processed and a response is ready.
 *
 * @param ring_handle Ring handle containing response ring to enqueue to.
 * @param status response status.
 * @param addr pointer to encoded dma address of data.
 * @param count number of sectors allocated for corresponding command
 * @param successful_count number of sectors successfully read/written
 * @param id command ID to identify which command the response is for.
 *
 * @return -1 when response ring is full, 0 on success.
 */
static inline int sddf_blk_enqueue_resp(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_response_status_t status,
                                        uintptr_t addr,
                                        uint16_t count,
                                        uint16_t successful_count,
                                        uint32_t id)
{
    if (sddf_blk_resp_ring_full(ring_handle)) {
        return -1;
    }

    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].status = status;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].addr = addr;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].count = count;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].successful_count = successful_count;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].id = id;

    THREAD_MEMORY_RELEASE();
    ring_handle->resp_ring->write_idx++;

    return 0;
}

/**
 * Dequeue an element from the command ring buffer.
 *
 * @param ring Ring handle containing command ring to dequeue from.
 * @param code pointer to command code.
 * @param addr pointer to encoded dma address of data.
 * @param sector pointer to  sector number to read/write.
 * @param count pointer to number of sectors to read/write.
 * @param id pointer to store command ID.
 *
 * @return -1 when command ring is empty, 0 on success.
 */
static inline int sddf_blk_dequeue_cmd(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_command_code_t *code,
                                        uintptr_t *addr,
                                        uint32_t *sector,
                                        uint16_t *count,
                                        uint32_t *id)
{
    if (sddf_blk_cmd_ring_empty(ring_handle)) {
        return -1;
    }

    *code = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].code;
    *addr = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].addr;
    *sector = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].sector;
    *count = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].count;
    *id = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].id;

    THREAD_MEMORY_RELEASE();
    ring_handle->cmd_ring->read_idx++;

    return 0;
}

/**
 * Dequeue an element from a response ring buffer.
 *
 * @param ring Ring handle containing response ring to dequeue from.
 * @param status pointer to response status.
 * @param addr pointer to encoded dma address of data.
 * @param count pointer to number of sectors allocated for corresponding command
 * @param successful_count pointer to number of sectors successfully read/written
 * @param id pointer to storing command ID to idenfity which command this response is for.
 * @return -1 when response ring is empty, 0 on success.
 */
static inline int sddf_blk_dequeue_resp(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_response_status_t *status,
                                        uintptr_t *addr,
                                        uint16_t *count,
                                        uint16_t *successful_count,
                                        uint32_t *id)
{
    if (sddf_blk_resp_ring_empty(ring_handle)) {
        return -1;
    }

    *status = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].status;
    *addr = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].addr;
    *count = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].count;
    *successful_count = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].successful_count;
    *id = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].id;

    THREAD_MEMORY_RELEASE();
    ring_handle->resp_ring->read_idx++;

    return 0;
}

/**
 * Set the plug of the command ring to true.
 *
 * @param ring_handle Ring handle containing command ring to check for plug.
*/
static inline void sddf_blk_cmd_ring_plug(sddf_blk_ring_handle_t *ring_handle) {
    ring_handle->cmd_ring->plugged = true;
}

/**
 * Set the plug of the command ring to false.
 *
 * @param ring Ring handle containing command ring to check for plug.
*/
static inline void sddf_blk_cmd_ring_unplug(sddf_blk_ring_handle_t *ring_handle) {
    ring_handle->cmd_ring->plugged = false;
}

/**
 * Check the current value of the command ring plug.
 *
 * @param ring Ring handle containing command ring to check for plug.
 *
 * @return true when command ring is plugged, false when unplugged.
*/
static inline bool sddf_blk_cmd_ring_plugged(sddf_blk_ring_handle_t *ring_handle) {
    return ring_handle->cmd_ring->plugged;
}

// @ericc: need to refactor, currently unused as we are using driver VM
/**
 * Dequeue an element from a ring buffer.
 * This function is intended for use by the driver, to collect a pointer
 * into this structure to be passed around as a id.
 *
 * @param ring Ring buffer to dequeue from.
 * @param addr pointer to the address of where to store buffer address.
 * @param len pointer to variable to store length of data dequeueing.
 * @param cookie pointer to store a pointer to this particular entry.
 *
 * @return -1 when ring is empty, 0 on success.
 */
// static int driver_dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len, uint32_t **cookie)
// {
//     if (ring_empty(ring)) {
//         return -1;
//     }

//     *addr = ring->buffers[ring->read_idx % ring->size].encoded_addr;
//     *len = ring->buffers[ring->read_idx % ring->size].len;
//     *id = &ring->buffers[ring->read_idx % ring->size];

//     THREAD_MEMORY_RELEASE();
//     ring->read_idx++;

//     return 0;
// }
