/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

#include "blk_config.h"

#define BLK_VIRT_CHANNEL 0

blk_queue_handle_t blk_queue;
/* set by microkit */
blk_storage_info_t *blk_storage_info;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
uintptr_t blk_data;

#define KEEP_REPEATING_COMMANDS false
#define NUM_READ_BLOCKS   6
#define NUM_WRITE_BLOCKS  5
_Static_assert(NUM_READ_BLOCKS > NUM_WRITE_BLOCKS, "#read must be greater than #write");

/* we write something different than the index into position i for clarity */
#define BYTE_ADJUST(i) ((i + 3) & 0xFF)

void print_some_data()
{
    /* start from the read (from card) section, which should contain the data we wrote to the card */
    volatile uint8_t *block_data = (volatile uint8_t *)(blk_data);
    sddf_printf("[   0] = 0x%x\n", block_data[   0]);
    sddf_printf("[   1] = 0x%x\n", block_data[   1]);
    sddf_printf("[   2] = 0x%x\n", block_data[   2]);
    sddf_printf("[   3] = 0x%x\n", block_data[   3]);
    sddf_printf("[ 508] = 0x%x\n", block_data[ 508]);
    sddf_printf("[ 509] = 0x%x\n", block_data[ 509]);
    sddf_printf("[ 510] = 0x%x\n", block_data[ 510]);
    sddf_printf("[ 511] = 0x%x\n", block_data[ 511]);
    sddf_printf("[ 512] = 0x%x\n", block_data[ 512]);
    // ^ that was one 512 block, but we should see a 4096 block of increasing digits
    sddf_printf("[ 513] = 0x%x\n", block_data[ 513]);
    sddf_printf("[ 514] = 0x%x\n", block_data[ 514]);
    sddf_printf("[ 515] = 0x%x\n", block_data[ 515]);
    sddf_printf("[ 516] = 0x%x\n", block_data[ 516]);
    sddf_printf("[4092] = 0x%x\n", block_data[4092]);
    sddf_printf("[4093] = 0x%x\n", block_data[4093]);
    sddf_printf("[4094] = 0x%x\n", block_data[4094]);
    sddf_printf("[4095] = 0x%x\n", block_data[4095]);
    sddf_printf("[4096] = 0x%x\n", block_data[4096]);
    sddf_printf("[4097] = 0x%x\n", block_data[4097]);
    // all the way up to NUM_WRITE_BLOCKS - 1 (as we wrote data there)
    sddf_printf("[NW-3] = 0x%x\n", block_data[NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE - 3]);
    sddf_printf("[NW-2] = 0x%x\n", block_data[NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE - 2]);
    sddf_printf("[NWB-] = 0x%x\n\n", block_data[NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE - 1]);
    // but not past it! these should all be zeroes, as we didn't write data to the card; and we assume the card is empty
    sddf_printf("[NWB=] = 0x%x\n", block_data[NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE + 0]);
    sddf_printf("[NWB+] = 0x%x\n", block_data[NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE + 1]);
    sddf_printf("[NW++] = 0x%x\n", block_data[NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE + 2]);
    // all the way up to NUM_READ_BLOCKS, where we stopped reading
    sddf_printf("[NR-2] = 0x%x\n", block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE - 2]);
    sddf_printf("[NR-1] = 0x%x\n\n", block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE - 1]);

    // then we should encounter the writing data that we prefilled into our memory, before writing it to the card
    // which should be some increasing numbers.
    sddf_printf("[NRB=] = 0x%x\n", block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE + 0]);
    sddf_printf("[NR+1] = 0x%x\n", block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE + 1]);
    sddf_printf("[NR+2] = 0x%x\n", block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE + 2]);
    sddf_printf("[NR+3] = 0x%x\n", block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE + 3]);
}

void ensure_data_is_correct()
{
    volatile uint8_t *block_data = (volatile uint8_t *)blk_data;

    for (int i = 0; i < NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE; i++) {
        if (block_data[i] != BYTE_ADJUST(i)) {
            assert(!"The data we wrote, then read from the device doesn't match!\n");
        }
    }
    for (int i = NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE; i < NUM_READ_BLOCKS * BLK_TRANSFER_SIZE; i++) {
        if (block_data[i] != 0x0) {
            assert(!"The data that was on the card, which we didn't touch, wasn't still zeroed!\n");
        }
    }
    for (int i = 0; i < BLK_TRANSFER_SIZE; i++) {
        if (block_data[NUM_READ_BLOCKS * BLK_TRANSFER_SIZE + i] != BYTE_ADJUST(i)) {
            assert(!"The original memory that we wrote to the device was overwritten, when it should have been left alone by the read command\n");
        }
    }

    sddf_printf("Client read/write data is correct!\n");
}

void send_commands(void)
{
    uint32_t data_address = 0;

    /* Setup a data region with a region to read into from the card, initially zeroed
        then another region to write to the card with.

        Note: Read region is before the write region, so that we can ensure
              that reading into it doesn't overwrite our original data we wrote from
              i.e. a driver bug
    */
    volatile uint8_t *block_data = (volatile uint8_t *)blk_data;
    for (int i = 0; i < NUM_READ_BLOCKS * BLK_TRANSFER_SIZE; i++) {
        block_data[i] = 0x0;
    }
    for (int i = 0; i < NUM_WRITE_BLOCKS * BLK_TRANSFER_SIZE; i++) {
        // we offset it so it's not 0 at start or end
        block_data[i + NUM_READ_BLOCKS * BLK_TRANSFER_SIZE] = BYTE_ADJUST(i);
    }

    /* Request to write data, then read it back */

    // write some zeroed data first; just our zeroed read blocks as a test.
    int err = blk_enqueue_req(&blk_queue, BLK_REQ_WRITE, 0x0, data_address, NUM_READ_BLOCKS, /* req ID */ 0);
    assert(!err);
    err = blk_enqueue_req(&blk_queue, BLK_REQ_WRITE, 0x0 + NUM_READ_BLOCKS * BLK_TRANSFER_SIZE, data_address,
                          NUM_WRITE_BLOCKS, /* req ID */ 1);
    assert(!err);
    err = blk_enqueue_req(&blk_queue, BLK_REQ_BARRIER, 0, 0, 0, /* req ID */ 2);
    assert(!err);
    err = blk_enqueue_req(&blk_queue, BLK_REQ_FLUSH, 0, 0, 0, /* req ID */ 3);
    assert(!err);
    // read some random stuff
    err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, 0x0, 0x0, NUM_READ_BLOCKS, /* req ID */ 4);
    assert(!err);
    // do a second read test to check this
    err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, 0x0, data_address, NUM_READ_BLOCKS, /* req ID */ 5);
    assert(!err);

    microkit_notify(BLK_VIRT_CHANNEL);
}

void notified(microkit_channel ch)
{
    if (ch != BLK_VIRT_CHANNEL) {
        assert(!"bad channel?");
    }

    if (blk_queue_length_resp(&blk_queue) < 6 /* the number of requests we sent */) {
        /* just wait until all requests are serviced */
        return;
    }

    /* dequeue and check the requests succeeded */
    blk_resp_status_t status = BLK_RESP_OK;
    uint16_t success_count;
    uint32_t id = 0;
    while (blk_queue_length_resp(&blk_queue) > 0) {
        assert(!blk_dequeue_resp(&blk_queue, &status, &success_count, &id));
        if (status != BLK_RESP_OK) {
            sddf_printf("request failed: stat: %u, id: %u\n", status, id);
            assert(!"failed");
        }

    }

    if (!KEEP_REPEATING_COMMANDS) {
        print_some_data();
    }
    ensure_data_is_correct();
    if (KEEP_REPEATING_COMMANDS) {
        send_commands();
    }
}

void init(void)
{
    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_CAPACITY_CLI0);

    /* Busy wait until blk device is ready */
    while (!blk_storage_is_ready(blk_storage_info));

    sddf_printf("Hello from client\n");

    /* The third partition on the SD card (after Uboot & Linux) is made empty
       so we don't overwrite anything important.
    */
    assert(blk_partition_mapping[0] == 2);
    send_commands();
}
