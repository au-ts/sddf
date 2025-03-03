/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <assert.h>
#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/util/string.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/timer/client.h>

#define LOG_CLIENT(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define QUEUE_SIZE 512
#define VIRT_CH 0
#define TIMER   1

#define BENCHMARK_TOTAL_SIZE ONE_HUNDRED_MB
#define BLK_TRANSFER_SIZE 4096
#define BENCHMARK_CHUNKSIZE ONE_HUNDRED_MB
#define ONE_HUNDRED_MB 0x6400000
#define ONE_MB 0x100000
#define BLOCK_READ_INTERVAL ONE_MB
#define BYTES_TO_MB 1048576.0         // 1 MB = 1048576 bytes

static_assert(BENCHMARK_TOTAL_SIZE % BENCHMARK_CHUNKSIZE == 0, "The chunksize must be aligned to the total size");
static_assert(BENCHMARK_CHUNKSIZE % BLK_TRANSFER_SIZE == 0, "The chunksize must be a multiple of the transfer size");

blk_storage_info_t *blk_storage_info;
uintptr_t blk_request;
uintptr_t blk_response;
uintptr_t blk_data;

uint64_t blk_data_paddr;

uint64_t request_id = 1;

static blk_queue_handle_t blk_queue;

enum benchmark_state {
    START,
    WRITE,
    READ,
    FINISH,
};

enum benchmark_state benchmark_state = START;

uint64_t start_time = 0;
uint64_t end_time = 0;

bool benchmark()
{
    switch (benchmark_state) {
    case START: {
        LOG_CLIENT("Benchmark: START state\n");

        int err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, blk_data_paddr, 0, 2, request_id);
        
        // assert(!err);

        request_id++;
        benchmark_state = READ;

        break;
    }
    case READ: {
        LOG_CLIENT("Benchmark: READ state\n");
        /* Check that our previous write was successful */
        blk_resp_status_t status = -1;
        uint16_t count = -1;
        uint32_t id = -1;
        int err = blk_dequeue_resp(&blk_queue, &status, &count, &id);
        // assert(!err);
        // assert(status == BLK_RESP_OK);
        // assert(count == 2);
        // assert(id == 0);

        uint64_t read_start_sector = 1024;
        uint64_t times = 0;
        // A static check should be added here to check if the read/write requests may go out of disk capacity boundary
        while (BENCHMARK_TOTAL_SIZE - times * BENCHMARK_CHUNKSIZE) {
            err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, blk_data_paddr + times * BENCHMARK_CHUNKSIZE, 
                    read_start_sector + times * (BENCHMARK_CHUNKSIZE / BLK_TRANSFER_SIZE + BLOCK_READ_INTERVAL / BLK_TRANSFER_SIZE), 
                    (BENCHMARK_CHUNKSIZE / BLK_TRANSFER_SIZE), request_id);
            request_id++;
            times++;
            // assert(!err);
        }

        benchmark_state = FINISH;

        start_time = sddf_timer_time_now(TIMER);

        break;
    }
    case FINISH: {
        end_time = sddf_timer_time_now(TIMER);

        // assert(end_time > start_time);

        uint64_t time_passed = end_time - start_time;
        
        LOG_CLIENT("Benchmark: FINISH state\n");

        double speed_bytes_per_sec = (double)BENCHMARK_TOTAL_SIZE * 1000000000.0 / time_passed;

        // Convert to MB/s
        double speed_mb_per_sec = speed_bytes_per_sec / BYTES_TO_MB;

        sddf_dprintf("Benchmarking speed: %.5fByte/Second\n", speed_bytes_per_sec);
        sddf_dprintf("Benchmark Speed: %.5f MB/s\n", speed_mb_per_sec);
        sddf_dprintf("Time has passed: %ld nanosecond\n", time_passed);

        LOG_CLIENT("Benchmark: successfully finished!\n");

        return true;
    }
    default:
        LOG_CLIENT_ERR("internal error, invalid state\n");
        // assert(false);
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

    benchmark();
    microkit_notify(VIRT_CH);
}

void notified(microkit_channel ch)
{
    // assert(ch == VIRT_CH);

    if (!benchmark()) {
        microkit_notify(VIRT_CH);
    }
}
