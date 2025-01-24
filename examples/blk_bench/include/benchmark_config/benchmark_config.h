/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Values in terms of include/sddf//blk/queue.h: BLK_TRANSFER_SIZE
// sizes for debugging SD card block bundle boundries (odroidc4 for SDXC can pack up to 0x1ff of 512 byte blocks, so boundry every 255.5 KiB)
//#define BENCHMARK_BLOCKS_PER_REQUEST (uint16_t[]) {1, 2, 4, 8, 32, 63, 64, 128, 256, 512, 640, 768, 896, 1024, 2048}
// sizes 2X at each step: 4KiB, 8KiB 16KiB, 32KiB, 64KiB, 128KiB, 256KiB, 512KiB, 1MiB, 2MiB, 4MiB, 8MiB
#define BENCHMARK_BLOCKS_PER_REQUEST (uint16_t[]) {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048}
// Need to be a max of 8 MiB (client data region in SDF)
#define REQUEST_COUNT (uint16_t[]) {256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256, 256}
//#define REQUEST_COUNT (uint32_t[]) {10, 10, 10, 10, 10}
#define BENCHMARK_RUN_COUNT ((int) sizeof(BENCHMARK_BLOCKS_PER_REQUEST)/sizeof(uint16_t))
#define BENCHMARK_INDIVIDUAL_RUN_REPEATS 10
// comment out when benchmarking, if defined: performs validation of all IO operations (using RANDOM_WRITE and SEQUENTIAL_WRITE traces and reading them back)
//#define VALIDATE_IO_OPERATIONS

// TODO: add defines for default clock speed for odroid c4's CPU, to compute throughput in terms of time
// in MHz
//#define ODROID_CPU_CLKFREQ_MHZ 1200
#define ODROID_CPU_CLKFREQ_MHZ 1000

// benchmark runs
enum run_benchmark_state {
    START_BENCHMARK,
    THROUGHPUT_RANDOM_READ,
    THROUGHPUT_RANDOM_WRITE,
    THROUGHPUT_SEQUENTIAL_READ,
    THROUGHPUT_SEQUENTIAL_WRITE,
    LATENCY_READ,
    LATENCY_WRITE,
    VALIDATE_RANDOM_WRITE,
    VALIDATE_SEQUENTIAL_WRITE,
};
const char* human_readable_run_benchmark_state[] = {
    "START_BENCHMARK",
    "THROUGHPUT_RANDOM_READ",
    "THROUGHPUT_RANDOM_WRITE",
    "THROUGHPUT_SEQUENTIAL_READ",
    "THROUGHPUT_SEQUENTIAL_WRITE",
    "LATENCY_READ",
    "LATENCY_WRITE",
    "VALIDATE_RANDOM_WRITE",
    "VALIDATE_SEQUENTIAL_WRITE",
};
