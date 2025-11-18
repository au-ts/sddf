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
    uint64_t time_start = sddf_timer_time_now(config.driver_id);

    uint32_t freq = 0;

    uint32_t res = sddf_dvfs_get_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, &freq);

    if (res != 0) {
        sddf_printf_("DVFS Client: Fail to get the frequency\n");
        return;
    }

    cpu_intensive_loop();

    uint64_t time_mid = sddf_timer_time_now(config.driver_id);

    res = sddf_dvfs_set_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, CPU_INFO[0].opptable[1].freq_hz);

    if (res != 0) {
        sddf_printf_("DVFS Client: Fail to set the frequency\n");
        return;
    }

    cpu_intensive_loop();

    uint64_t time_end = sddf_timer_time_now(config.driver_id);

    sddf_printf_("%lu ns takes under Frequency: %d", time_mid - time_start, freq);

    sddf_printf_("%lu ns takes under Frequency: %lu", time_end - time_mid, CPU_INFO[0].opptable[1].freq_hz);
}

void notified(microkit_channel ch) {}