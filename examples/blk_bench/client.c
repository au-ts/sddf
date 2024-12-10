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
#include <sddf/serial/queue.h>
#include <serial_config.h>
#include <benchmark_config.h>
#include <blk_config.h>

/*
 * This header is generated by the build system, it contains the data we want
 * to write to the block device
 */
#include "basic_data.h"
//#include "sddf/util/fence.h"

#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define VIRT_CH 0
#define SERIAL_TX_CH 1
#define START_PMU 2
#define STOP_PMU 3
#define BENCH_RUN_CH 4


char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;

blk_storage_info_t *blk_storage_info;
uintptr_t blk_request;
uintptr_t blk_response;
char* blk_data;
uintptr_t blk_client0_data_paddr;

static blk_queue_handle_t blk_queue;

void panic(char* reason) {
    LOG_CLIENT("Panic! %s\n", reason);
    __builtin_trap();
}

void dequeue_and_validate(uint16_t exp_count) {
    blk_resp_status_t status;
    uint16_t count;
    uint32_t id;
    int err = blk_dequeue_resp(&blk_queue, &status, &count, &id);
    if (err)
        panic("could not dequeue");
    if (status != BLK_RESP_OK)
        panic("invalid resp status");
    if (count != exp_count)
        panic("invalid count");
    // XXX cant validate ID, as requesrts can be out of order, would need to dequeue and check all
    //if (id != exp_id)
    //    panic("invalid id");
}


enum run_benchmark_state run_benchmark_state = START_BENCHMARK;
bool virtualiser_replied = false;
uint8_t benchmark_size_idx = 0;
 // only read/write 1024*1024 sectors in (4GiB in), Avoid U-Boot
 // continuosly advance read start to avoid caching benefits
uint64_t read_start_sector = 1024*1024;
// write at 16 GiB in
uint64_t write_start_sector = 4*1024*1024;
int benchmark_run_idx = 0;

void handle_random_operations_run(blk_req_code_t request_code, uint32_t start_sector, uint32_t interval, char* run_type, enum run_benchmark_state next_state);

bool run_benchmark() {
    switch(run_benchmark_state) {
        case START_BENCHMARK:
            /* make sure the driver is working properly */
            if (!virtualiser_replied) {
                LOG_CLIENT("run_benchmark: START state,verifying if a simple read succeeds...\n");
                int err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, 0x10000, 0, 2, 0);
                assert(!err);
                microkit_notify(VIRT_CH);
            } else {
                dequeue_and_validate(2);
                LOG_CLIENT("run_benchmark: simple read successful.\n");
                run_benchmark_state = THROUGHPUT_RANDOM_READ;
                virtualiser_replied = false;
                run_benchmark();
            }
            break;
        case THROUGHPUT_RANDOM_READ:
            /* Perform REQUEST_COUNT[benchmark_size_idx] random READs, from 4KiB write size up to 8MiB */
            handle_random_operations_run(BLK_REQ_READ, read_start_sector, BLOCK_READ_WRITE_INTERVAL, "RANDOM_READ", THROUGHPUT_RANDOM_WRITE);
            break;
        case THROUGHPUT_RANDOM_WRITE:
            /* Perform QUEUE_SIZE WRITEs, from 4KiB write size up to 128MiB (x8 at each step) */
            // write out garbage for the WRITE_REQUESTs
            if (benchmark_size_idx == 0)
                for (int i = 0; i < BLK_DATA_REGION_SIZE_CLI0; ++i) {
                    blk_data[i] = i % 255;
                }

            handle_random_operations_run(BLK_REQ_WRITE, write_start_sector, BLOCK_READ_WRITE_INTERVAL, "RANDOM_WRITE", THROUGHPUT_SEQUENTIAL_READ);
            break;
        case THROUGHPUT_SEQUENTIAL_READ:
            handle_random_operations_run(BLK_REQ_READ, read_start_sector, 0, "SEQUENTIAL_READ", THROUGHPUT_SEQUENTIAL_WRITE);
            break;
        case THROUGHPUT_SEQUENTIAL_WRITE:
            if (benchmark_size_idx == 0)
                for (int i = 0; i < BLK_DATA_REGION_SIZE_CLI0; ++i) {
                    blk_data[i] = i % 255;
                }
            handle_random_operations_run(BLK_REQ_WRITE, write_start_sector, 0, "SEQUENTIAL_WRITE", LATENCY_READ);
            break;
        case LATENCY_READ:
            // Perform QUEUE_SIZE random reads, only measure latency of each read
            // XXX to verify: will latency differ with request read size? or will it be constant
            // XXX if varies, maybe can be merged into THROUGHPUT_RANDOM_READ
            break;
        case LATENCY_WRITE:
            // Per
            // Returns true, as this is the final benchmark. System will sit idle afterwards
            return true;
            break;
        default:
            LOG_CLIENT_ERR("internal error, invalid state\n");
            assert(false);
    }
    return false;
}

void handle_random_operations_run(blk_req_code_t request_code, uint32_t start_sector, uint32_t interval, char* run_type, enum run_benchmark_state next_state) {
    if (!virtualiser_replied) {
        LOG_CLIENT("run_benchmark: THROUGHPUT_%s: %d requests of %d transfer blocks at a time.\n"
                "Reading start sector: %u\n", run_type, REQUEST_COUNT[benchmark_size_idx],
                BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx], start_sector);
        if (blk_queue_length_req(&blk_queue) != 0 || blk_queue_length_resp(&blk_queue) != 0)
            panic("blk response or request queue not empty!");
        for (uint32_t i = 0; i != REQUEST_COUNT[benchmark_size_idx]; ++i) {
            /* Read or WRITE BENCHMARK_BLOCKS_PER_REQUEST blocks for this benchmark run, stepping by
             * size of request + 16 MiB (driver doesn't do any smart reordering, should mean that SD
             * card's caching has no effect)
             */
            // XXX always reading to the SAME address space in the shared memory region
            uintptr_t io_or_offset = 0;//i * BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx] * BLK_TRANSFER_SIZE;
            uint32_t block_number = start_sector + i * BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx] + \
                                 i * interval / BLK_TRANSFER_SIZE;
            uint16_t count = BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx];
            //sddf_printf("client: io_or_offset 0x%lx, block_number: %d, count: %d\n", io_or_offset, block_number, count);

            int err = blk_enqueue_req(&blk_queue, request_code, io_or_offset, block_number, count, i);
            assert(!err);
        }
        // start the PMU and notify the virtualiser to start processing the input queue
        microkit_notify(START_PMU);
        microkit_notify(VIRT_CH);
    } else if (blk_queue_length_resp(&blk_queue) == REQUEST_COUNT[benchmark_size_idx] ) {
        // virtualiser replied -> queue processed!
        microkit_notify(STOP_PMU);
        // clean up the queue
        sddf_printf("queue size before dequeue: %d\n", blk_queue_length_resp(&blk_queue));
        for (uint32_t i = 0; i != REQUEST_COUNT[benchmark_size_idx]; ++i) {
            dequeue_and_validate(BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx]);
        }
        sddf_printf("queue size after dequeue: %d\n", blk_queue_length_resp(&blk_queue));
        benchmark_size_idx = (benchmark_size_idx + 1) % BENCHMARK_RUN_COUNT;
        if (benchmark_size_idx == 0) {
            benchmark_run_idx = (benchmark_run_idx + 1) % BENCHMARK_INDIVIDUAL_RUN_REPEATS;
            if (benchmark_run_idx == 0) {
                run_benchmark_state = next_state;
                sddf_printf("run_benchmark: finished all BENCHMARK_BLOCKS_PER_REQUEST for THROUGHPUT_%s\n", run_type);
            } else {
                sddf_printf("run_benchmark: finished %d/%d run for THROUGHPUT_%s\n", benchmark_run_idx, BENCHMARK_INDIVIDUAL_RUN_REPEATS, run_type);
            }
        }
        virtualiser_replied = false;
    }
}

void init(void)
{
    serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue, serial_tx_data);
    // TODO: fix the below - currently will crash if debug_build as it is compiled with sddf_util and not sddf_util_debug.
    // FIX: modify makefile to add sddf_util_debug if MICORKIT_CONFIG=debug ??
#ifndef CONFIG_DEBUG_BUILD
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);
#endif

    LOG_CLIENT("starting.\n");

    blk_queue_init(&blk_queue, (blk_req_queue_t *)blk_request, (blk_resp_queue_t *)blk_response, blk_cli_queue_capacity(microkit_name));

    /* Want to print out configuration information, so wait until the config is ready. */
    LOG_CLIENT("check if device config ready\n");
    while (!blk_storage_is_ready(blk_storage_info));
    LOG_CLIENT("device config ready\n");

    LOG_CLIENT("device size: 0x%lx bytes\n", blk_storage_info->capacity * BLK_TRANSFER_SIZE);
}

void notified(microkit_channel ch)
{
    //LOG_CLIENT("notified %u\n", ch);
    switch (ch) {
        case VIRT_CH:
            //LOG_CLIENT("notified from virtualiser %u\n", ch);
            // Virtualiser replied, handle appropriately
            virtualiser_replied = true;
            run_benchmark();
            break;
        case SERIAL_TX_CH:
            // Nothing to do
            break;
        case BENCH_RUN_CH:
            // TODO: Start the required benchmark
            virtualiser_replied = false;
            LOG_CLIENT("client notified to start bench.\n");
            run_benchmark();
            break;
        default:
            LOG_CLIENT_ERR("received notification on unexpected channel: %u\n", ch);
            break;
    }
}
