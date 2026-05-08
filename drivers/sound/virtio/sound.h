/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <sddf/util/printf.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("SND DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_dprintf("SND DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

struct virtio_snd_config {
    uint32_t jacks;
    uint32_t streams;
    uint32_t chmaps;
};

static void virtio_snd_print_config(volatile struct virtio_snd_config *config)
{
    LOG_DRIVER("jacks: 0x%x\n", config->jacks);
    LOG_DRIVER("streams: 0x%x\n", config->streams);
    LOG_DRIVER("chmaps: 0x%x\n", config->chmaps);
}
