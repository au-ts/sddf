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
#include <sddf/blk/config.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>

#include <serial_config.h>

#include <sddf/benchmark/config.h>
#include <benchmark_config.h>
#include <benchmark_traces.h>
// XXX: How to set the SIZE of blk data memory region in meta.py??
//#include <blk_config.h>

#include <sddf/benchmark/config.h>

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

__attribute__((__section__(".benchmark_blk_client_config"))) benchmark_blk_client_config_t benchmark_blk_config;

__attribute__((__section__(".blk_client_config"))) blk_client_config_t blk_config;

#define DO_LOG_DEBUG

#ifdef DO_LOG_DEBUG
#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...)
#define LOG_CLIENT_ERR(...)
#endif
#define panic(...) do{ sddf_printf("CLIENT|Panic! "); sddf_printf(__VA_ARGS__); __builtin_trap(); } while(0)

serial_queue_handle_t serial_tx_queue_handle;
static blk_queue_handle_t blk_queue;
blk_storage_info_t *blk_storage_info;
char* blk_data;


enum run_benchmark_state run_benchmark_state = START_BENCHMARK;
bool virtualiser_replied = false;
uint8_t benchmark_size_idx = 0;
int benchmark_run_idx = 0;
#ifdef VALIDATE_IO_OPERATIONS
uint16_t validation_req_idx = 0;
#endif

void dequeue_and_validate(uint16_t exp_count) {
    blk_resp_status_t status;
    uint16_t count;
    uint32_t id;
    int err = blk_dequeue_resp(&blk_queue, &status, &count, &id);
    if (err)
        panic("could not dequeue\n");
    if (status != BLK_RESP_OK)
        panic("invalid resp status\n");
    if (count != exp_count)
        panic("invalid count\n");
    // XXX cant validate ID, as requesrts can be out of order, would need to dequeue and check all
    //if (id != exp_id)
    //    panic("invalid id");
}

#ifdef VALIDATE_IO_OPERATIONS
void fill_blk_data(const uint32_t *offsets_array, uint16_t max_num_reqs, uint16_t max_req_size_blocks) {
    // Fills the blk_data region with a repeating pattern of block offsets.
    // This pattern repeats until max request size can be satifisfied + BLK_TRANSFER_SIZE*REQUEST_COUNT
    // TODO: for now, assumes constant REQUEST_COUNT for all requests, divisible by 4 (sizeof(uint32_t)
    uint32_t *blk_data_32 = ((uint32_t*) blk_data);
    for (uint32_t i = 0; i < (int) ((max_req_size_blocks + max_num_reqs)*BLK_TRANSFER_SIZE/sizeof(uint32_t)); ++i) {
        blk_data_32[i] = offsets_array[i % max_num_reqs];
    }
}

void validate_write_data(const uint32_t *offsets_array, uint16_t arr_offset) {
    // assumes blocks were filled in with fill_blk_data()
    if (!virtualiser_replied) {
        int err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, 0x0, offsets_array[arr_offset], BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx], 0);
        assert(!err);
        microkit_notify(blk_config.virt.id);
    } else {
        if (blk_queue_length_resp(&blk_queue) != 0) {
            dequeue_and_validate(BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx]);
            uint32_t *blk_data_32 = ((uint32_t*) blk_data);
            for (uint32_t i = 0; i < (int) ((BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx]*BLK_TRANSFER_SIZE)/sizeof(uint32_t)); ++i) {
                if (blk_data_32[i] != offsets_array[(i + (int) (arr_offset*BLK_TRANSFER_SIZE/sizeof(uint32_t))) % REQUEST_COUNT[benchmark_size_idx]]) {
                    panic("Wrong value read back during validation\n"
                          "validation_req_idx: %d, arr_offset: %d. Expected val: %d, read val: %d. Stage: %s\n",
                          validation_req_idx, i,
                          offsets_array[(i + (int) (arr_offset*BLK_TRANSFER_SIZE/sizeof(uint32_t))) % REQUEST_COUNT[benchmark_size_idx]],
                          blk_data_32[i], human_readable_run_benchmark_state[run_benchmark_state]);
                }
            }
            sddf_printf("validated blocks in request: %d\n", arr_offset);
        } else {
            /* potentially race cond from previous request chain -> received ping from virt after processing all response queue */
            virtualiser_replied = false;
        }
    }
}
#endif

void advance_benchmark_idx_and_stage(enum run_benchmark_state current_state, enum run_benchmark_state next_state) {
    /* by default, remain at current state (or for validation stage -> return to appropriate benchmark) */
    run_benchmark_state = current_state;
    benchmark_size_idx = (benchmark_size_idx + 1) % BENCHMARK_RUN_COUNT;
    if (benchmark_size_idx == 0) {
#ifndef VALIDATE_IO_OPERATIONS
        benchmark_run_idx = (benchmark_run_idx + 1) % BENCHMARK_INDIVIDUAL_RUN_REPEATS;
#else
        /* If VALIDATE_IO_OPERATIONS, only do a single run iteration for each benchmark size */
        benchmark_run_idx = 0;
#endif
        if (benchmark_run_idx == 0) {
            LOG_CLIENT("run_benchmark: finished all BENCHMARK_BLOCKS_PER_REQUEST for %s\n", human_readable_run_benchmark_state[run_benchmark_state]);
            run_benchmark_state = next_state;
        } else {
            LOG_CLIENT("run_benchmark: finished %d/%d run for %s\n", benchmark_run_idx, BENCHMARK_INDIVIDUAL_RUN_REPEATS, human_readable_run_benchmark_state[run_benchmark_state]);
        }
    }
}

void handle_random_operations_run(blk_req_code_t request_code, const uint32_t* request_offsets_arr, enum run_benchmark_state next_state);

/* tracks if dummy data for writing to block device is populated in shared memory region */
bool dummy_write_data_populated = false;
bool run_benchmark() {
     if(!blk_storage_is_ready(blk_storage_info)) {
         /* If SD card is switched off (power cycle) - turn it back on and wait for it to be ready */
#if defined(MICROKIT_BOARD_odroidc4)
        LOG_CLIENT("SD card was off at benchmark start, turning back on.\n");
        int err = blk_enqueue_req(&blk_queue, BLK_REQ_SD_ON, 0, 0, 0, 0);
        assert(!err);
        microkit_notify(blk_config.virt.id);
        // XXX: need to implement proper hotplugging handling, see usdhc work: https://github.com/au-ts/sddf/pull/180/files
        // timeout and wait for SD to be on for 1 s
        sddf_timer_set_timeout(timer_config.driver_id, 1e7);
        //while(!blk_storage_is_ready(blk_storage_info));
        return false;
#elif defined(MICROKIT_BOARD_maaxboard)
        panic("SD card off/not ready but power cycling not implemented for Maaxboard!\n");
#else
        panic("SD card off/not ready but power cycling not implemented for current board\n");
#endif
     }
    switch(run_benchmark_state) {
        case START_BENCHMARK:
            /* make sure the driver is working properly */
#ifndef VALIDATE_IO_OPERATIONS
            if (!virtualiser_replied) {
                LOG_CLIENT("run_benchmark: START state,verifying if a simple read succeeds...\n");
                int err = blk_enqueue_req(&blk_queue, BLK_REQ_READ, 0x10000, 0, 2, 1);
                assert(!err);
                microkit_notify(blk_config.virt.id);
            } else {
                dequeue_and_validate(2);
                LOG_CLIENT("run_benchmark: simple read successful.\n");
                run_benchmark_state = THROUGHPUT_RANDOM_READ;
                virtualiser_replied = false;
                run_benchmark();
            }
#else
            run_benchmark_state = THROUGHPUT_RANDOM_WRITE;
            virtualiser_replied = false;
            run_benchmark();
#endif
            break;
        case THROUGHPUT_RANDOM_READ:
            /* Perform REQUEST_COUNT[benchmark_size_idx] random READs, from 4KiB write size up to 8MiB */
            dummy_write_data_populated = false;
            handle_random_operations_run(BLK_REQ_READ, RANDOM_READ_OFFSETS_ARR[benchmark_size_idx], THROUGHPUT_RANDOM_WRITE);
            break;
        case THROUGHPUT_RANDOM_WRITE:
            /* Perform REQUEST_COUNT[benchmark_size_idx] WRITEs, from 4KiB write size up to 128MiB (x8 at each step) */
#ifndef VALIDATE_IO_OPERATIONS
            /* write out garbage for the WRITE_REQUESTs ONLY at the beginning of this benchmark type */
            if (!dummy_write_data_populated)
            {
                for (int i = 0; i < blk_config.data.size; ++i) {
                    blk_data[i] = i % 255;
                }
                dummy_write_data_populated = true;
            }
#else
            fill_blk_data(RANDOM_WRITE_OFFSETS_ARR[benchmark_size_idx],  REQUEST_COUNT[benchmark_size_idx], BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx]);
#endif
            handle_random_operations_run(BLK_REQ_WRITE, RANDOM_WRITE_OFFSETS_ARR[benchmark_size_idx], THROUGHPUT_SEQUENTIAL_READ);
            break;
        case VALIDATE_RANDOM_WRITE:
#ifdef VALIDATE_IO_OPERATIONS
            validate_write_data(RANDOM_WRITE_OFFSETS_ARR[benchmark_size_idx], validation_req_idx);
            if(virtualiser_replied) {
                /* Validated req id: validation_req_idx. Increment */
                ++validation_req_idx;
                virtualiser_replied = false;
                if (validation_req_idx == REQUEST_COUNT[benchmark_size_idx]) {
                    validation_req_idx = 0;
                    advance_benchmark_idx_and_stage(THROUGHPUT_RANDOM_WRITE, THROUGHPUT_SEQUENTIAL_WRITE);
                }
                run_benchmark();
            }
#else
            panic("Validation stage reached with VALIDATE_IO_OPERATIONS not being defined!\n");
#endif
            break;
        case THROUGHPUT_SEQUENTIAL_READ:
            dummy_write_data_populated = false;
            handle_random_operations_run(BLK_REQ_READ, SEQUENTIAL_READ_OFFSETS_ARR[benchmark_size_idx], THROUGHPUT_SEQUENTIAL_WRITE);
            break;
        case THROUGHPUT_SEQUENTIAL_WRITE:
#ifndef VALIDATE_IO_OPERATIONS
            if (!dummy_write_data_populated)
            {
                for (int i = 0; i < blk_config.data.size; ++i) {
                    blk_data[i] = i % 255;
                }
                dummy_write_data_populated = true;
            }
#else
            fill_blk_data(SEQUENTIAL_WRITE_OFFSETS_ARR[benchmark_size_idx],  REQUEST_COUNT[benchmark_size_idx], BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx]);
#endif
            handle_random_operations_run(BLK_REQ_WRITE, SEQUENTIAL_WRITE_OFFSETS_ARR[benchmark_size_idx], LATENCY_READ);
            break;
        case VALIDATE_SEQUENTIAL_WRITE:
#ifdef VALIDATE_IO_OPERATIONS
            validate_write_data(SEQUENTIAL_WRITE_OFFSETS_ARR[benchmark_size_idx], validation_req_idx);
            if(virtualiser_replied) {
                /* Validated req id: validation_req_idx. Increment */
                ++validation_req_idx;
                virtualiser_replied = false;
                if (validation_req_idx == REQUEST_COUNT[benchmark_size_idx]) {
                    validation_req_idx = 0;
                    advance_benchmark_idx_and_stage(THROUGHPUT_SEQUENTIAL_WRITE, LATENCY_READ);
                }
                run_benchmark();
            }
#else
            panic("Validation stage reached with VALIDATE_IO_OPERATIONS not being defined!\n");
#endif
            break;
        case LATENCY_READ:
            dummy_write_data_populated = false;
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

void handle_random_operations_run(blk_req_code_t request_code, const uint32_t* request_offsets_arr, enum run_benchmark_state next_state) {
    if (!virtualiser_replied) {
        LOG_CLIENT("run_benchmark: %s: %d requests of %d transfer blocks at a time.\n",
                human_readable_run_benchmark_state[run_benchmark_state], REQUEST_COUNT[benchmark_size_idx],
                BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx]);
        if (blk_queue_length_req(&blk_queue) != 0 || blk_queue_length_resp(&blk_queue) != 0)
            panic("blk response or request queue not empty!\n");
        for (uint32_t i = 0; i != REQUEST_COUNT[benchmark_size_idx]; ++i) {
            /* Read or WRITE BENCHMARK_BLOCKS_PER_REQUEST blocks for this benchmark run,
             * Replaying the trace workload from the benchmark_traces.h generated file.
             * XXX reading/writing to overlapping memory addresses (does not matter for benchmarking,
             * for validation need to read one block at a time) For validation purposes, read/write address
             * is increasing by 1 page at each step (enforced page alignment).
             */
            uintptr_t io_or_offset = BLK_TRANSFER_SIZE*i;
            /*
             * NOTE: block_number is in terms of TRANSFER_SIZE, and its the offset from the start of
             * the partition belonging to the client. Virtualiser will then add the required offset
             * so driver gets the exact offset into the SD card in terms of no of TRANSFER_SIZE chunks
             */
            uint32_t block_number = request_offsets_arr[i];
            uint16_t count = BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx];
            LOG_CLIENT("offset: %ld, block num: %d, count: %d\n", io_or_offset, block_number, count);
            int err = blk_enqueue_req(&blk_queue, request_code, io_or_offset, block_number, count, i);
            assert(!err);
        }
        // start the PMU and notify the virtualiser to start processing the input queue
        microkit_notify(benchmark_blk_config.start_ch);
        microkit_notify(blk_config.virt.id);
    } else if (blk_queue_length_resp(&blk_queue) == REQUEST_COUNT[benchmark_size_idx] ) {
        // virtualiser replied -> queue processed!
        microkit_notify(benchmark_blk_config.stop_ch);
        // clean up the queue
        for (uint32_t i = 0; i != REQUEST_COUNT[benchmark_size_idx]; ++i) {
            uint16_t count = BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx];
            dequeue_and_validate(count);
        }
        if (request_code == BLK_REQ_WRITE || request_code == BLK_REQ_READ) {
            /*
             * Power cycle SD card for 10s, to reset the write loci: https://trustworthy.systems/publications/nicta_slides/8311.pdf (slide 20)
             * The 10s timeout is handled by benchmark_blk.c, after receiving STOP_PMU channel notification.
             */
#if defined(MICROKIT_BOARD_odroidc4)
            LOG_CLIENT("Powering off SD card.\n");
            int err = blk_enqueue_req(&blk_queue, BLK_REQ_SD_OFF, 0, 0, 0, 0);
            __atomic_store_n(&blk_storage_info->ready, false, __ATOMIC_RELEASE);
            assert(!err);
            microkit_notify(blk_config.virt.id);
#elif defined(MICROKIT_BOARD_maaxboard)
            LOG_CLIENT("Power cycling not implemented for Maaxboard - performing benchmark without powercycling!.\n");
#else
            LOG_CLIENT("Power cycling not implemented for current board - performing benchmark without powercycling!.\n");
#endif
        }
        virtualiser_replied = false;
#ifdef VALIDATE_IO_OPERATIONS
        /* If validating, step to the appropriate Validation stage (either for RANDOM WRITE or SEQUENTIAL) */
        switch (run_benchmark_state) {
            case THROUGHPUT_RANDOM_WRITE:
                run_benchmark_state = VALIDATE_RANDOM_WRITE;
                break;
            case THROUGHPUT_SEQUENTIAL_WRITE:
                run_benchmark_state = VALIDATE_SEQUENTIAL_WRITE;
                break;
            default:
                LOG_CLIENT("CURRENT STAGE: %s\n", human_readable_run_benchmark_state[run_benchmark_state]);
                panic("Unimplemented IO operation validation stage for current benchmark stage.\n");
        }
#else
        /* Otherwise, step to the next iteration/next stage */
        advance_benchmark_idx_and_stage(run_benchmark_state, next_state);
#endif
    }
}

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    assert(timer_config_check_magic(&timer_config));
    assert(blk_config_check_magic(&blk_config));
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size, serial_config.tx.data.vaddr);
    // TODO: fix the below - currently will crash if debug_build as it is compiled with sddf_util and not sddf_util_debug.
    // FIX: modify makefile to add sddf_util_debug if MICORKIT_CONFIG=debug ??
#ifndef CONFIG_DEBUG_BUILD
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);
#endif
    LOG_CLIENT("starting.\n");
    blk_queue_init(&blk_queue, blk_config.virt.req_queue.vaddr, blk_config.virt.resp_queue.vaddr, blk_config.virt.num_buffers);
    /* Want to print out configuration information, so wait until the config is ready. */
    blk_storage_info = blk_config.virt.storage_info.vaddr;
    blk_data = blk_config.data.vaddr;
    while (!blk_storage_is_ready(blk_storage_info));
    LOG_CLIENT("device config ready\n");
    LOG_CLIENT("device size: 0x%lx bytes\n", blk_storage_info->capacity * BLK_TRANSFER_SIZE);
}

void notified(microkit_channel ch)
{
    //LOG_CLIENT("notified %u\n", ch);
    if (ch == serial_config.tx.id) {
        // Nothing to do
        return;
    } else if (ch == blk_config.virt.id) { 
        //LOG_CLIENT("notified from virtualiser %u\n", ch);
        /* Virtualiser replied, handle appropriately */
        virtualiser_replied = true;
        run_benchmark();
    } else if (ch == benchmark_blk_config.bench_run_ch) {

        virtualiser_replied = false;
        LOG_CLIENT("client notified to start bench.\n");
        run_benchmark();
    } else if (ch == timer_config.driver_id) {
        /* timer replied after timeout, sanity check if it is valid. */
        if (!blk_storage_is_ready(blk_storage_info)) {
            LOG_CLIENT("timer notified that SD card should be on and initialised by now!\n");
            __atomic_store_n(&blk_storage_info->ready, true, __ATOMIC_RELEASE);
            run_benchmark();
        } else {
            panic("Received notification from timer but blk_storage_info->ready was already true!\n");
        }
    } else {
        panic("received notification on unexpected channel: %u\n", ch);
    }
}
