/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/util/string.h>
#include <ethernet_config.h>
#include <stdint.h>

/* Total number of cores on the board. */
#define MAX_CORES 4

/* Total number of PDs being tracked during the benchmark. */
#define NUM_PDS_TO_TRACK 8

/* The core of the benchmark PD which is last in the notification chain.
   The benchmark PD on this core receives START and STOP notifications,
   but does not send them. */
#define LAST_CORE 1

typedef struct {
    uint16_t pd_id; /* ID of the PD. */
    uint16_t pd_core; /* Core of the PD. */
    char *pd_name; /* Name of the PD. */
} pd_core_info_t;

pd_core_info_t pd_core_info[NUM_PDS_TO_TRACK] = {
    { 1, 0, NET_DRIVER_NAME }, /* Ethernet driver. */
    { 2, 1, NET_VIRT_RX_NAME }, /* Rx virtualiser. */
    { 3, 0, NET_VIRT_TX_NAME }, /* Tx virtualiser. */
    { 4, 1, NET_COPY0_NAME }, /* Copy component 0. */
    { 5, 1, NET_COPY1_NAME }, /* Copy component 1. */
    { 6, 1, NET_CLI0_NAME }, /* LWIP client 0. */
    { 7, 1, NET_CLI1_NAME }, /* LWIP client 1. */
    { 8, 1, NET_TIMER_NAME } /* Timer driver. */
};

typedef struct {
    uint64_t core_bitmap; /* Bitmap of client IDs on this core. */
    uint32_t core_value; /* Core of this benchmark process. */
    uint32_t max_core_id; /* Maximum ID of client on this core. */
    bool last_core; /* Whether this bench process is the last in the notification chain. */
} core_config_t;

static void bench_core_config_info(char *pd_name, core_config_t *core_config)
{
    core_config->max_core_id = 0;
    core_config->last_core = false;

    if (!sddf_strcmp(pd_name, "bench0")) {
        core_config->core_value = 0;
    } else if (!sddf_strcmp(pd_name, "bench1")) {
        core_config->core_value = 1;
    } else if (!sddf_strcmp(pd_name, "bench2")) {
        core_config->core_value = 2;
    } else if (!sddf_strcmp(pd_name, "bench3")) {
        core_config->core_value = 3;
    } else {
        return;
    }

    if (core_config->core_value == LAST_CORE) {
        core_config->last_core = true;
    }

    for (uint16_t i = 0; i < NUM_PDS_TO_TRACK; i++) {
        if (pd_core_info[i].pd_core == core_config->core_value) {
            core_config->core_bitmap |= (1 << pd_core_info[i].pd_id);
            if (pd_core_info[i].pd_id > core_config->max_core_id) {
                core_config->max_core_id = pd_core_info[i].pd_id;
            }
        }
    }
}

static uint16_t bench_active_cores()
{
    uint16_t active_cores = 0;
    for (uint16_t i = 0; i < NUM_PDS_TO_TRACK; i++) {
        active_cores |= (1 << pd_core_info[i].pd_core);
    }

    return active_cores;
}

static char *pd_id_to_name(uint16_t pd_id)
{
    for (uint16_t i = 0; i < NUM_PDS_TO_TRACK; i++) {
        if (pd_core_info[i].pd_id == pd_id) {
            return pd_core_info[i].pd_name;
        }
    }

    return NULL;
}
