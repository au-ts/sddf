/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Values in terms of include/sddf//blk/queue.h: BLK_TRANSFER_SIZE
// decided on runs: 4KiB, 32KiB, 256KiB, 2MiB, 8MiB
#define BENCHMARK_BLOCKS_PER_REQUEST (uint32_t[]) {1, 8, 64, 512, 2048}
//, 4096, 32768}
// Need to be a max of 8 MiB (client data region in SDF)
//#define REQUEST_COUNT (uint32_t[]) {256, 256, 32, 4, 1}
#define REQUEST_COUNT (uint32_t[]) {256, 256, 256, 256, 256}
#define BENCHMARK_RUN_COUNT ((int) sizeof(BENCHMARK_BLOCKS_PER_REQUEST)/sizeof(uint32_t))
// 1 MiB interval to counter the caching of block device's sequential READs
// XXX and to counter the batching of WRITE commits
#define BLOCK_READ_WRITE_INTERVAL 0x1600000

// TODO: add defines for default clock speed for odroid c4's CPU, to compute throughput in terms of time
// in MHz
#define ODROID_CPU_CLKFREQ 1200

// benchmark runs
enum run_benchmark_state {
    START_BENCHMARK,
    THROUGHPUT_RANDOM_READ,
    THROUGHPUT_RANDOM_WRITE,
    LATENCY_READ,
    LATENCY_WRITE,
};
