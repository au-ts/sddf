/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

void notified(sddf_channel ch)
{
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");
}
