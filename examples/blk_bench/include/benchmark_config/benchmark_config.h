/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define QUEUE_SIZE 512 

// Values in terms of include/sddf//blk/queue.h: BLK_TRANSFER_SIZE
// decided on runs: 4KiB, 32KiB, 256KiB, 2MiB, 16MiB and 128MiB
#define BENCHMARK_BLOCKS_PER_REQUEST (uint32_t[]) {8, 1}//, 64, 512}
//, 512, 4096, 32768}
// Need to be a max of 8 MiB (client data region in SDF)
#define REQUEST_COUNT (uint32_t[]) {256, 256}//, 32, 4}
#define BENCHMARK_RUN_COUNT ((int) sizeof(BENCHMARK_BLOCKS_PER_REQUEST)/sizeof(uint32_t))
// 1 MiB interval to counter the caching of block device's sequential READs
// XXX and to counter the batching of WRITE commits
#define BLOCK_READ_WRITE_INTERVAL 0x100000

// TODO: add defines for default clock speed for odroid c4's CPU, to compute throughput in terms of time
// in MHz
#define ODROID_CPU_CLKFREQ 1200
