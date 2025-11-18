/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "microkit.h"
#include <sddf/dvfs/client.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>
#include <stdint.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

#define DVFS_CHANNEL 0
#define LOOP_LIMITATION 100000

void cpu_intensive_loop() {
    volatile int i;

    for (i = 0; i < LOOP_LIMITATION; i++) {

    }
}

void init(void) {
    uint32_t freq = 0;

    uint32_t res = sddf_dvfs_get_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, &freq);

    if (res != SDDF_DVFS_SUCCESS) {
        sddf_printf_("DVFS Client: Fail to get the frequency, Error: %d\n", res);
        return;
    }

    sddf_printf_("DVFS Client: BEGIN FIRST ROUND\n");

    uint64_t time_start_1 = sddf_timer_time_now(config.driver_id);

    cpu_intensive_loop();

    uint64_t time_end_1 = sddf_timer_time_now(config.driver_id);

    sddf_printf_("DVFS Client: BEGIN SECOND ROUND\n");

    res = sddf_dvfs_set_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, CPU_INFO[0].opptable[1].freq_hz);

    sddf_printf_("DVFS Client: TEST\n");

    if (res != SDDF_DVFS_SUCCESS) {
        sddf_printf_("DVFS Client: Fail to set the frequency, Error: %d\n", res);
        return;
    }

    sddf_printf_("DVFS Client: TEST\n");

    uint64_t time_start_2 = sddf_timer_time_now(config.driver_id);

    sddf_printf_("DVFS Client: TEST\n");

    cpu_intensive_loop();

    uint64_t time_end_2 = sddf_timer_time_now(config.driver_id);

    sddf_printf_("DVFS Client: TEST\n");

    sddf_printf_("%lu ns takes under Frequency: %d\n", time_end_1 - time_start_1, freq);

    sddf_printf_("%lu ns takes under Frequency: %d\n", time_end_2 - time_start_2, sddf_dvfs_get_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, &freq));

    sddf_printf_("DVFS Client: TEST\n");
}

void notified(microkit_channel ch) {}