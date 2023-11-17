/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include "util/include/util.h"
#include "util/include/fence.h"
#include "sddf_blk_shared_ringbuffer.h"

void sddf_blk_ring_init(sddf_blk_ring_handle_t *ring_handle,
                        sddf_blk_cmd_ring_buffer_t *command,
                        sddf_blk_resp_ring_buffer_t *response,
                        sddf_blk_desc_handle_t *desc_handle,
                        sddf_blk_freelist_handle_t *freelist_handle,
                        int buffer_init,
                        uint32_t command_size,
                        uint32_t response_size,
                        uint32_t num_data_buffers)
{
    ring_handle->cmd_ring = command;
    ring_handle->resp_ring = response;
    ring_handle->desc_handle = desc_handle;
    ring_handle->freelist_handle = freelist_handle;
    if (buffer_init) {
        assert(num_data_buffers <= SDDF_BLK_NUM_DATA_BUFFERS);
        assert(command_size <= SDDF_BLK_NUM_CMD_BUFFERS);
        assert(response_size <= SDDF_BLK_NUM_RESP_BUFFERS);
        ring_handle->cmd_ring->write_idx = 0;
        ring_handle->cmd_ring->read_idx = 0;
        ring_handle->cmd_ring->size = command_size;
        ring_handle->cmd_ring->notify_writer = false;
        ring_handle->cmd_ring->notify_reader = false;
        ring_handle->cmd_ring->plugged = false;
        
        ring_handle->resp_ring->write_idx = 0;
        ring_handle->resp_ring->read_idx = 0;
        ring_handle->resp_ring->size = response_size;
        ring_handle->resp_ring->notify_writer =false;
        ring_handle->resp_ring->notify_reader = false;
        
        ring_handle->desc_handle->size = num_data_buffers;
        for (unsigned int i=0; i<num_data_buffers; i++) {
            ring_handle->desc_handle->descs[i].has_next = false;
            ring_handle->desc_handle->descs[i].len = 0;
        }

        ring_handle->freelist_handle->head = 0;
        ring_handle->freelist_handle->tail = num_data_buffers - 1;
        ring_handle->freelist_handle->size = num_data_buffers;
        ring_handle->freelist_handle->num_free = num_data_buffers;
        /* Initialise freelist */
        for (unsigned int i=0; i<num_data_buffers-1; i++) {
            ring_handle->freelist_handle->freelist[i] = i+1;
        }
        ring_handle->freelist_handle->freelist[num_data_buffers - 1] = -1;
    }
}

bool sddf_blk_desc_full(sddf_blk_ring_handle_t *ring_handle, uint32_t count)
{
    assert(count > 0);
    if (count > ring_handle->freelist_handle->num_free) {
        return true;
    }
    return false;
}

// @ericc: no memory barrier needed as get_desc and free_desc are only called from the same side
int sddf_blk_get_desc(sddf_blk_ring_handle_t *ring_handle, uint32_t *desc_head_idx, uint32_t count)
{
    assert(count > 0);
    if (sddf_blk_desc_full(ring_handle, count)) {
        return -1;
    }
    
    // Initialise descriptor chain
    uint32_t curr_desc_idx = ring_handle->freelist_handle->head;
    for (uint32_t i=0; i<count-1; i++) {
        // Attach curr descriptor to next free descriptor
        ring_handle->desc_handle->descs[curr_desc_idx].next = ring_handle->freelist_handle->freelist[curr_desc_idx];
        ring_handle->desc_handle->descs[curr_desc_idx].has_next = true;
        // Go to next free descriptor
        curr_desc_idx = ring_handle->freelist_handle->freelist[curr_desc_idx];
    }

    // Initialise last descriptor of chain
    ring_handle->desc_handle->descs[curr_desc_idx].has_next = false;

    // Give caller the head of the descriptor chain
    *desc_head_idx = ring_handle->freelist_handle->head;

    // Update number of free descriptors
    ring_handle->freelist_handle->num_free -= count;
    // Update head to the next free descriptor
    ring_handle->freelist_handle->head = ring_handle->freelist_handle->freelist[curr_desc_idx];
    
    return 0;
}

void sddf_blk_free_desc(sddf_blk_ring_handle_t *ring_handle, uint32_t desc_head_idx)
{
    assert(ring_handle->freelist_handle->num_free < SDDF_BLK_NUM_DATA_BUFFERS);
    assert(desc_head_idx < ring_handle->desc_handle->size);
    assert(desc_head_idx >= 0);

    // If the descriptor array was completely filled, head will be stale so we need to update it
    if (ring_handle->freelist_handle->num_free == 0) {
        ring_handle->freelist_handle->head = desc_head_idx;
    }

    // Length of descriptor chain
    uint32_t count = 1;

    // Set tail entry in freelist to desc_head_idx
    ring_handle->freelist_handle->freelist[ring_handle->freelist_handle->tail] = desc_head_idx;

    uint32_t curr_desc_idx = desc_head_idx;
    uint32_t prev_desc_idx;
    while (ring_handle->desc_handle->descs[curr_desc_idx].has_next) {
        // Detach current descriptor from the chain
        ring_handle->desc_handle->descs[curr_desc_idx].has_next = false;
        // Go to next descriptor
        prev_desc_idx = curr_desc_idx;
        curr_desc_idx = ring_handle->desc_handle->descs[curr_desc_idx].next;
        // Chain prev descriptor to the curr descriptor
        ring_handle->freelist_handle->freelist[prev_desc_idx] = curr_desc_idx;
        count++;
    }

    // Update num_free descriptors
    ring_handle->freelist_handle->num_free += count;
    // Update tail to the last descriptor in the chain
    ring_handle->freelist_handle->tail = curr_desc_idx;
}