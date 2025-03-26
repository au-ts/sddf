/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/**
 * GUID Partition Table
 *
 * https://en.wikipedia.org/wiki/GUID_Partition_Table
 * */

#define GPT_SECTOR_SIZE 512
#define GPT_PARTITION_INFO_CODE 0x1
#define GPT_PARTITION_INFO_MIRROR_CODE 0x2
#define GPT_HEADER_SIGNATURE "EFI PART"

struct gpt_partition_header {
    char signature[8];
    uint32_t revision;
    uint32_t header_size;
    uint32_t crc32_header;
    uint32_t reserved;
    uint64_t lba_header;
    uint64_t lba_alt_header;
    uint64_t block_first;
    uint64_t block_last;
    uint8_t guid[16];
    uint64_t lba_start;
    uint32_t num_entries;
    uint32_t entry_size;
    uint32_t crc32_entry_array;
} __attribute__((packed));

struct gpt_partition_entry {
    uint8_t guid_type[16];
    uint8_t guid_unique[16];
    uint64_t lba_start;
    uint64_t lba_end;
    uint64_t attributes;
    char name[72];
} __attribute__((packed));
