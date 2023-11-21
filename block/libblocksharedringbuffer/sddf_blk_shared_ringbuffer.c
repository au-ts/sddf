/*
 * Copyright 2023, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
// #include "util/include/util.h"
#include "sddf_blk_shared_ringbuffer.h"

#define AVAIL_BITMAP(ring_handle, idx) \
    (ring_handle->data->avail_bitmap[idx])

#define AVAIL_BITPOS(ring_handle) \
    (ring_handle->data->avail_bitpos)

#define DATA_NUM_BUFFERS(ring_handle) \
    (ring_handle->data->num_buffers)

#define BITPOS_TO_ADDR(ring_handle, pos) \
    (ring_handle->data->addr + ((uintptr_t)pos * SDDF_BLK_DATA_BUFFER_SIZE))

#define ADDR_TO_BITPOS(ring_handle, addr) \
    ((uint32_t)(((uintptr_t)addr - ring_handle->data->addr) / SDDF_BLK_DATA_BUFFER_SIZE))

// @ericc: maybe put this into util.c?
#define MASK_ABOVE_POSITION_INCLUSIVE(position) (~(((uint32_t)1 << (position)) - 1))

#define MASK_BELOW_POSITION_EXCLUSIVE(position) (((uint32_t)1 << (position)) - 1)

void sddf_blk_ring_init(sddf_blk_ring_handle_t *ring_handle,
                        sddf_blk_cmd_ring_buffer_t *command,
                        sddf_blk_resp_ring_buffer_t *response,
                        sddf_blk_data_t *data,
                        int buffer_init,
                        uint32_t command_size,
                        uint32_t response_size,
                        uintptr_t data_addr,
                        uint32_t data_num_buffers)
{
    ring_handle->cmd_ring = command;
    ring_handle->resp_ring = response;
    ring_handle->data = data;
    if (buffer_init) {
        assert(command_size <= SDDF_BLK_NUM_CMD_BUFFERS);
        assert(response_size <= SDDF_BLK_NUM_RESP_BUFFERS);
        assert(data_num_buffers <= SDDF_BLK_NUM_DATA_BUFFERS);
        ring_handle->cmd_ring->write_idx = 0;
        ring_handle->cmd_ring->read_idx = 0;
        ring_handle->cmd_ring->size = command_size;
        ring_handle->cmd_ring->plugged = false;
        
        ring_handle->resp_ring->write_idx = 0;
        ring_handle->resp_ring->read_idx = 0;
        ring_handle->resp_ring->size = response_size;

        ring_handle->data->addr = data_addr;
        ring_handle->data->avail_bitpos = 0;
        ring_handle->data->num_buffers = data_num_buffers;
        for (int i = 0; i < data; i++) {
            ring_handle->data->avail_bitmap[i] = 1;
        }
    }
}

int sddf_blk_data_full(sddf_blk_ring_handle_t *ring_handle, uint16_t count)
{
    if (count > DATA_NUM_BUFFERS(ring_handle)) {
        return true;
    }

    // @ericc: Technically don't need to define so many variables here, but it's easier to read
    // Check for all 0's in the next count many bits
    unsigned int start_bitpos = AVAIL_BITPOS(ring_handle); // can be a macro
    unsigned int end_bitpos = AVAIL_BITPOS(ring_handle) + count; // can be macro
    unsigned int curr_idx = start_bitpos / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE;
    unsigned int end_idx = end_bitpos / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE; // can be macro
    uint32_t mask;
    if (curr_idx != end_idx) {
        // Check the bits in the first index
        mask = MASK_ABOVE_POSITION_INCLUSIVE(start_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        if (AVAIL_BITMAP(ring_handle, curr_idx) & mask != mask) {
            return true;
        }
        curr_idx++;

        // Check the bits in indices between the first and last
        mask = MASK_ABOVE_POSITION_INCLUSIVE(0);
        for (; curr_idx != end_idx; curr_idx++) {
            if (AVAIL_BITMAP(ring_handle, curr_idx) & mask != mask) {
                return true;
            }
        }

        // Check the bits in the last index
        mask = MASK_BELOW_POSITION_EXCLUSIVE(end_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        if (AVAIL_BITMAP(ring_handle, end_idx) & mask != mask) {
            return true;
        }
    } else {
        // Check the bits in the index
        // Create a mask as such 00000000_00001111_11110000_00000000, check whether section in middle is all 1's, if not then its full
        mask = MASK_ABOVE_POSITION_INCLUSIVE(start_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE) & MASK_BELOW_POSITION_EXCLUSIVE(end_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        if (AVAIL_BITMAP(ring_handle, curr_idx) & mask != mask) {
            return true;
        }
    }

    return false;
}

int sddf_blk_data_get_buffer(sddf_blk_ring_handle_t *ring_handle, uintptr_t *addr, uint16_t count)
{
    if (sddf_blk_data_full(ring_handle, count)) {
        return -1;
    }

    if (sddf_blk_data_end(ring_handle, count)) {
        return -2;
    }

    *addr = BITPOS_TO_ADDR(ring_handle, AVAIL_BITPOS(ring_handle));

    // Set the next count many bits as unavailable
    unsigned int start_bitpos = AVAIL_BITPOS(ring_handle);
    unsigned int end_bitpos = AVAIL_BITPOS(ring_handle) + count;
    unsigned int curr_idx = start_bitpos / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE;
    unsigned int end_idx = end_bitpos / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE;
    uint32_t mask;
    if (curr_idx != end_idx) {
        // Set the bits in the first index
        mask = MASK_BELOW_POSITION_EXCLUSIVE(start_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        AVAIL_BITMAP(ring_handle, curr_idx) &= mask;
        curr_idx++;

        // Set the bits in indices between the first and last
        mask = MASK_BELOW_POSITION_EXCLUSIVE(0);
        for (; curr_idx != end_idx; curr_idx++) {
            AVAIL_BITMAP(ring_handle, curr_idx) &= mask;
        }

        // Set the bits in the last index
        mask = MASK_ABOVE_POSITION_INCLUSIVE(end_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        AVAIL_BITMAP(ring_handle, end_idx) &= mask;
    } else {
        // Set the bits in the index
        // Create a mask as such 11111111_11110000_00001111_11111111, set some section in middle to be 0
        mask = MASK_BELOW_POSITION_EXCLUSIVE(start_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE) & MASK_ABOVE_POSITION_INCLUSIVE(end_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        AVAIL_BITMAP(ring_handle, curr_idx) &= mask;
    }

    // Update the bitpos
    if (end_bitpos == DATA_NUM_BUFFERS(ring_handle)) {
        end_bitpos = 0;
    }
    AVAIL_BITPOS(ring_handle) = end_bitpos;

    return 0;
}

int sddf_blk_data_free_buffer(sddf_blk_ring_handle_t *ring_handle, uintptr_t addr, uint16_t count)
{
    unsigned int start_bitpos = ADDR_TO_BITPOS(ring_handle, addr);
    unsigned int end_bitpos = start_bitpos + count;
    unsigned int curr_idx = start_bitpos / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE;
    unsigned int end_idx = end_bitpos / SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE;
    uint32_t mask;

    // Freeing buffers that overflow the data region
    if (start_bitpos + count > DATA_NUM_BUFFERS(ring_handle)) {
        return -1;
    }

    // Set the next many bits from the bit corresponding with addr as available
    if (curr_idx != end_idx) {
        // Set the bits in the first index
        mask = MASK_ABOVE_POSITION_INCLUSIVE(start_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        AVAIL_BITMAP(ring_handle, curr_idx) |= mask;
        curr_idx++;

        // Set the bits in indices between the first and last
        mask = MASK_ABOVE_POSITION_INCLUSIVE(0);
        for (; curr_idx != end_idx; curr_idx++) {
            AVAIL_BITMAP(ring_handle, curr_idx) |= mask;
        }

        // Set the bits in the last index
        mask = MASK_BELOW_POSITION_EXCLUSIVE(end_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        AVAIL_BITMAP(ring_handle, end_idx) |= mask;
    } else {
        // Set the bits in the index
        // Create a mask as such 00000000_00001111_11110000_00000000, set all bits in the middle section to 1.
        mask = MASK_ABOVE_POSITION_INCLUSIVE(start_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE) & MASK_BELOW_POSITION_EXCLUSIVE(end_bitpos % SDDF_BLK_AVAIL_BITMAP_ELEM_SIZE);
        AVAIL_BITMAP(ring_handle, curr_idx) |= mask;
    }

    return 0;
}