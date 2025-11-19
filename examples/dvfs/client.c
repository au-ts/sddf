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

#define LOOP_LIMIT 5000000

void cpu_intensive_loop() {
    volatile int i;

    for (i = 0; i < LOOP_LIMIT; i++) {

    }
}

int test_cpu_freq(uint64_t core_freq) {
    uint32_t res = sddf_dvfs_set_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, core_freq);
    
    if (res != SDDF_DVFS_SUCCESS) {
        sddf_printf_("DVFS Client: Fail to get the frequency, Error: %d\n", res);
        return 1;
    }

    uint32_t freq = 0;

    res = sddf_dvfs_get_freq(DVFS_CHANNEL, CPU_INFO[0].core_ident, &freq);

    if (res != SDDF_DVFS_SUCCESS) {
        sddf_printf_("DVFS Client: Fail to get the frequency, Error: %d\n", res);
        return 1;
    }

    sddf_printf_("\nDVFS Client: CURRENT FREQ: %d\n", freq);

    uint64_t time_start = sddf_timer_time_now(config.driver_id);

    cpu_intensive_loop();

    uint64_t time_end = sddf_timer_time_now(config.driver_id);

    sddf_printf_("DVFS Client: %lu ns was used for running the test\n", time_end - time_start);

    return 0;
}

void init(void) {
    test_cpu_freq(CPU_INFO[0].opptable[0].freq_hz);

    test_cpu_freq(CPU_INFO[0].opptable[1].freq_hz);

    test_cpu_freq(CPU_INFO[0].opptable[2].freq_hz);
}

void notified(microkit_channel ch) {}