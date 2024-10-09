/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

// #define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("CONSOLE DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("CONSOLE DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define VIRTIO_CONSOLE_F_SIZE 0
#define VIRTIO_CONSOLE_F_MULTIPORT 1
#define VIRTIO_CONSOLE_F_EMERG_WRITE 2

static void virtio_console_print_features(uint64_t features)
{
    if (features & ((uint64_t)1 << VIRTIO_CONSOLE_F_SIZE)) {
        LOG_DRIVER("    VIRTIO_CONSOLE_F_SIZE\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_CONSOLE_F_MULTIPORT)) {
        LOG_DRIVER("    VIRTIO_CONSOLE_F_MULTIPORT\n");
    }
    if (features & ((uint64_t)1 << VIRTIO_CONSOLE_F_EMERG_WRITE)) {
        LOG_DRIVER("    VIRTIO_CONSOLE_F_EMERG_WRITE\n");
    }
    virtio_print_reserved_feature_bits(features);
}
