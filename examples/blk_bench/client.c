/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/util/string.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>

/*
 * Add benchmarking specific functions for controlling PMU.
 */
//#include <sddf/benchmark/sel4bench.h>

/*
 * This header is generated by the build system, it contains the data we want
 * to write to the block device
 */
#include "basic_data.h"
#include "sddf/util/fence.h"

#define LOG_CLIENT(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define QUEUE_SIZE 128
#define VIRT_CH 0

blk_storage_info_t *blk_storage_info;
uintptr_t blk_request;
uintptr_t blk_response;
uintptr_t blk_data;

static blk_queue_handle_t blk_queue;

enum test_basic_state {
    START,
    WRITE,
    READ,
    FINISH,
};


enum test_basic_state test_basic_state = START;

bool test_basic()
{
    switch (test_basic_state) {
    case START: {
        LOG_CLIENT("basic: START state, start benchmark counters.\n");
        //sel4bench_reset_counters();
        //// ensure mem regs are written to
        //THREAD_MEMORY_RELEASE();
        //sel4bench_start_counters(benchmark_bf);
        // We assume that the data fits into two blocks
        assert(basic_data_len <= BLK_TRANSFER_SIZE * 2);

        // Copy our testing data into the block data region
        char *data_dest = (char *)blk_data;
        sddf_memcpy(data_dest, basic_data, basic_data_len);
        // XXX: szymix testign
        char extra_text[50] = "random text to be added";
        sddf_memcpy(data_dest+basic_data_len, extra_text, 50);
        LOG_CLIENT("Copied in some more data!");
        // XXX: end szymix testing

        int err = blk_enqueue_req(&blk_queue, BLK_REQ_WRITE, 0, 0, 2, 0);
        assert(!err);

        test_basic_state = READ;

        break;
    }
    case READ: {
        //LOG_CLIENT("basic: READ state\n");
        //sel4bench_get_counters(benchmark_bf, &counter_values[0]);
        //sel4bench_stop_counters(benchmark_bf);
        //sddf_printf("{\n");
        //for (int i = 0; i < ARRAY_SIZE(benchmarking_events); i++) {
        //    sddf_printf("%s: %lX\n", counter_names[i], counter_values[i]);
        //}
        //sddf_printf("}\n");
        /* Check that our previous write was successful */
        blk_resp_status_t status = -1;
        uint16_t count = -1;
        uint32_t id = -1;
        int err = blk_dequeue_resp(&blk_queue, &status, &count, &id);
        assert(!err);
        assert(status == BLK_RESP_OK);
        assert(count == 2);
        assert(id == 0);

        // Setup the read
        // We do the read at a different offset into the data region
        err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, 0x10000, 0, 2, 0);
        assert(!err);

        test_basic_state = FINISH;

        break;
    }
    case FINISH: {
        LOG_CLIENT("basic: FINISH state\n");
        blk_resp_status_t status = -1;
        uint16_t count = -1;
        uint32_t id = -1;
        int err = blk_dequeue_resp(&blk_queue, &status, &count, &id);
        assert(!err);
        assert(status == BLK_RESP_OK);
        assert(count == 2);
        assert(id == 0);

        // Check that the read went okay
        char *read_data = (char *)(blk_data + 0x10000);
        for (int i = 0; i < basic_data_len; i++) {
            if (read_data[i] != basic_data[i]) {
                LOG_CLIENT_ERR("basic: mismatch in bytes at position %d\n", i);
            }
        }

        // XXX: prints up to 4140  (BLK_TRANSFER_SIZE//90 *90 + 90)  character (1 block and a bit)
        for (int i = 0; i < BLK_TRANSFER_SIZE; i += 90) {
            for (int j = 0; j < 90; j++) {
                sddf_dprintf("%c", read_data[i + j]);
            }
        }
        // read the rest of the second block
        for (int i = 4140; i < 2*BLK_TRANSFER_SIZE; i += 90) {
            for (int j = 0; j < 90; j++) {
                sddf_dprintf("%c", read_data[i + j]);
            }
        }
        sddf_dprintf("\n");

        LOG_CLIENT("basic: successfully finished!\n");

        return true;
    }
    default:
        LOG_CLIENT_ERR("internal error, invalid state\n");
        assert(false);
    }

    return false;
}

void init(void)
{
    LOG_CLIENT("starting\n");

    blk_queue_init(&blk_queue, (blk_req_queue_t *)blk_request, (blk_resp_queue_t *)blk_response, QUEUE_SIZE);

    /* Want to print out configuration information, so wait until the config is ready. */
    while (!blk_storage_is_ready(blk_storage_info));
    LOG_CLIENT("device config ready\n");

    LOG_CLIENT("device size: 0x%lx bytes\n", blk_storage_info->capacity * BLK_TRANSFER_SIZE);

    LOG_CLIENT("Initialise benchmarking, start all counterrs..\n");
    //sel4bench_init();
    //seL4_Word n_counters = sel4bench_get_num_counters();

    //counter_bitfield_t mask = 0;

    //for (seL4_Word counter = 0; counter < n_counters; counter++) {
    //    if (counter >= ARRAY_SIZE(benchmarking_events)) {
    //        break;
    //    }
    //    sel4bench_set_count_event(counter, benchmarking_events[counter]);
    //    mask |= BIT(counter);
    //}

    //sel4bench_reset_counters();
    //sel4bench_start_counters(mask);
    //benchmark_bf = mask;

    test_basic();
    microkit_notify(VIRT_CH);
}

void notified(microkit_channel ch)
{
    assert(ch == VIRT_CH);

    if (!test_basic()) {
        microkit_notify(VIRT_CH);
    }
}