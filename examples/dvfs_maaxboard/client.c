/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/clk/client.h>
#include <sddf/serial/config.h>
#include <sddf/timer/config.h>
#include <sddf/dvfs/client.h>
#include <sddf/dvfs/protocol.h>

#define DVFS_CHANNEL 0
#define LOOP_LIMIT 5000000

#ifdef CONFIG_PLAT_MAAXBOARD
#include <sddf/clk/imx8mq-bindings.h>
#define NUM_OPPS 4
#else
#error "The target board is not supported\n"
#endif

__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

void cpu_intensive_loop()
{
    volatile int i;

    for (i = 0; i < LOOP_LIMIT; i++) {}
}

int test_cpu_point(op_point_idx_t core_point)
{
    uint32_t res = sddf_dvfs_set_point(DVFS_CHANNEL, 0, core_point);

    if (res != SDDF_DVFS_SUCCESS) {
        sddf_printf_("DVFS Client: Fail to get the pointuency, Error: %d\n", res);
        return 1;
    }

    op_point_idx_t point = 0;

    res = sddf_dvfs_get_point(DVFS_CHANNEL, 0, &point);

    if (res != SDDF_DVFS_SUCCESS) {
        sddf_printf_("DVFS Client: Fail to get OPP, Error: %d\n", res);
        return 1;
    }

    sddf_printf_("\nDVFS Client: Point = %u\n", point);

    uint64_t time_start = sddf_timer_time_now(timer_config.driver_id);

    cpu_intensive_loop();

    uint64_t time_end = sddf_timer_time_now(timer_config.driver_id);

    sddf_printf_("DVFS Client: %lu ns was used for running the test\n", time_end - time_start);

    return 0;
}

void init(void)
{
    for (op_point_idx_t i = 0; i < NUM_OPPS; i++) {
        sddf_printf("Testing operating point #%u...\n", i);
        test_cpu_point(i);
    }
    sddf_printf("Completed test of all operating points!\n");
}

void notified(microkit_channel ch)
{
}

