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

/* Number of buffers the command ring is configured to have. */
#define SDDF_BLK_NUM_CMD_BUFFERS 1024
/* Number of buffers the response ring is configured to have. */
#define SDDF_BLK_NUM_RESP_BUFFERS 1024
/* Number of buffers the data region is configured to have. */
#define SDDF_BLK_NUM_DATA_BUFFERS 4096
/* Size of a single data buffer. Set to equal sector size. */
#define SDDF_BLK_DATA_BUFFER_SIZE 512

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

/* */
typedef struct sddf_blk_desc {
    uintptr_t addr; /* the encoded dma address storing data */
    uint32_t len; /* data in bytes occupied by the descriptor */
    uint32_t next; /* index to next descriptor in the chain */
    bool has_next; /* indicates whether this descriptor has a next descriptor */
} sddf_blk_desc_t;

/* */
typedef struct sddf_blk_command {
    sddf_blk_command_code_t code; /* command code */
    uint32_t desc; /* index to the first descriptor in a chain of descriptors */
    uint32_t sector; /* sector number to read/write */
    uint16_t count; /* number of sectors to read/write, also indicates the length of descriptor chain due to buf_size == sector_size */
    uint32_t id; /* stores command ID */
} sddf_blk_command_t;

/* */
typedef struct sddf_blk_response {
    sddf_blk_response_status_t status; /* response status */
    uint32_t desc; /* index to the first descriptor in a chain of descriptors */
    uint16_t count; /* number of sectors successfully read/written */
    uint32_t id; /* stores corresponding command ID */
} sddf_blk_response_t;

/* Circular buffer containing commands */
typedef struct sddf_blk_cmd_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffers in command ring buffer */
    bool notify_writer;
    bool notify_reader;
    bool plugged;
    sddf_blk_command_t buffers[SDDF_BLK_NUM_CMD_BUFFERS];
} sddf_blk_cmd_ring_buffer_t;

/* Circular buffer containing responses */
typedef struct sddf_blk_resp_ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size; /* number of buffers in response ring buffer */
    bool notify_writer;
    bool notify_reader;
    sddf_blk_response_t buffers[SDDF_BLK_NUM_RESP_BUFFERS];
} sddf_blk_resp_ring_buffer_t;

/* */
typedef struct sddf_blk_desc_handle {
    uint32_t size;
    sddf_blk_desc_t descs[SDDF_BLK_NUM_DATA_BUFFERS];
} sddf_blk_desc_handle_t;

/* */
typedef struct sddf_blk_freelist_handle {
    uint32_t head;
    uint32_t tail;
    uint32_t num_free;
    uint32_t size;
    uint32_t freelist[SDDF_BLK_NUM_DATA_BUFFERS];
} sddf_blk_freelist_handle_t;

/* A ring handle for enqueing/dequeuing into  */
typedef struct sddf_blk_ring_handle {
    sddf_blk_cmd_ring_buffer_t *cmd_ring;
    sddf_blk_resp_ring_buffer_t *resp_ring;
    sddf_blk_desc_handle_t *desc_handle;
    sddf_blk_freelist_handle_t *freelist_handle;
} sddf_blk_ring_handle_t;

/**
 * Initialise the shared ring buffer.
 *
 * @param ring_handle ring handle to use.
 * @param command pointer to command ring in shared memory.
 * @param response pointer to response ring in shared memory.
 * @param buffer_init 1 indicates the read and write indices in shared memory need to be initialised.
 *                    0 indicates they do not. Only one side of the shared memory regions needs to do this.
 * @param command_size number of buffers in command ring.
 * @param response_size number of buffers in response ring.
 * @param num_data_buffers number of buffer segments in data region. Length of descriptor array and freelist will match this.
 */
void sddf_blk_ring_init(sddf_blk_ring_handle_t *ring_handle,
                        sddf_blk_cmd_ring_buffer_t *command,
                        sddf_blk_resp_ring_buffer_t *response,
                        sddf_blk_desc_handle_t *desc_handle,
                        sddf_blk_freelist_handle_t *freelist_handle,
                        int buffer_init,
                        uint32_t command_size,
                        uint32_t response_size,
                        uint32_t num_data_buffers);

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
 * Check if there are free descriptors.
 *
 * @param ring_handle ring handle containing data descriptors.
 * @param count number of free descriptor(s) to retrieve.
 *
 * @return true indicates that "count" many free descriptors are not available, false when they are available.
 */
bool sddf_blk_desc_full(sddf_blk_ring_handle_t *ring_handle, uint32_t count);

/**
 * Try to retrieve free descriptors
 *
 * @param ring_handle ring handle containing data descriptors.
 * @param desc_head_idx pointer to head of descriptor index
 * @param count number of free descriptor(s) to retrieve.
 *
 * @return -1 indicates that "count" many free descriptors are not available, 0 when they are retrieved.
 */
int sddf_blk_get_desc(sddf_blk_ring_handle_t *ring_handle, uint32_t *desc_head_idx, uint32_t count);

/**
 * Free a chain of descriptors
 *
 * @param ring_handle ring handle containing data descriptors.
 * @param desc_head_idx pointer to head of descriptor index to free
 */
void sddf_blk_free_desc(sddf_blk_ring_handle_t *ring_handle, uint32_t desc_head_idx);

/**
 * Enqueue an element into the command ring buffer.
 *
 * @param ring_handle Ring handle containing command ring to enqueue to.
 * @param code command code.
 * @param desc index of head data descriptor chain
 * @param sector sector number to read/write.
 * @param count the number of sectors to read/write
 * @param id command ID to identify this command.
 *
 * @return -1 when command ring is full or data ring is full, 0 on success.
 */
static inline int sddf_blk_enqueue_cmd(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_command_code_t code,
                                        uint32_t desc,
                                        uint32_t sector,
                                        uint16_t count,
                                        uint32_t id)
{
    if (sddf_blk_cmd_ring_full(ring_handle)) {
        return -1;
    }

    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].code = code;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].desc = desc;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].sector = sector;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].count = count;
    ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->write_idx % ring_handle->cmd_ring->size].id = id;

    THREAD_MEMORY_RELEASE();
    ring_handle->cmd_ring->write_idx++;

    return 0;
}

/**
 * Enqueue an element into a used ring buffer.
 * This indicates the command has been processed and a response is ready.
 *
 * @param ring_handle Ring handle containing response ring to enqueue to.
 * @param status response status.
 * @param desc index of head data descriptor chain
 * @param count number of sectors successfully read/written
 * @param id command ID to identify which command the response is for.
 *
 * @return -1 when response ring is full, 0 on success.
 */
static inline int sddf_blk_enqueue_resp(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_response_status_t status,
                                        uint32_t desc,
                                        uint32_t count,
                                        uint32_t id)
{
    if (sddf_blk_resp_ring_full(ring_handle)) {
        return -1;
    }

    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].status = status;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].desc = desc;
    ring_handle->resp_ring->buffers[ring_handle->resp_ring->write_idx % ring_handle->resp_ring->size].count = count;
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
 * @param desc pointer to the index of head data descriptor chain
 * @param sector pointer to  sector number to read/write.
 * @param count pointer to number of sectors to read/write.
 * @param id pointer to store command ID.
 *
 * @return -1 when command ring is empty, 0 on success.
 */
static inline int sddf_blk_dequeue_cmd(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_command_code_t *code,
                                        uint32_t *desc,
                                        uint32_t *sector,
                                        uint16_t *count,
                                        uint32_t *id)
{
    if (sddf_blk_cmd_ring_empty(ring_handle)) {
        return -1;
    }

    *code = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].code;
    *desc = ring_handle->cmd_ring->buffers[ring_handle->cmd_ring->read_idx % ring_handle->cmd_ring->size].desc;
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
 * @param desc pointer to index of head data descriptor chain
 * @param count pointer to number of sectors successfully read/written
 * @param id pointer to storing command ID to idenfity which command this response is for.
 * @return -1 when response ring is empty, 0 on success.
 */
static inline int sddf_blk_dequeue_resp(sddf_blk_ring_handle_t *ring_handle,
                                        sddf_blk_response_status_t *status,
                                        uint32_t *desc,
                                        uint16_t *count,
                                        uint32_t *id)
{
    if (sddf_blk_resp_ring_empty(ring_handle)) {
        return -1;
    }

    *status = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].status;
    *desc = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].desc;
    *count = ring_handle->resp_ring->buffers[ring_handle->resp_ring->read_idx % ring_handle->resp_ring->size].count;
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
