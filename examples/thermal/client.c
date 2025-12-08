/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "microkit.h"
#include <sddf/thermal/client.h>
#include <sddf/pwm/client.h>
#include <sddf/util/printf.h>
#include <stdint.h>

sddf_channel thermal_channel;
sddf_channel pwm_channel;

#define ALERM_TEMP 40000

void init(void)
{
    sddf_printf_("Governor Starting\n");

    for (signed int i = 0; i < SENSOR_COUNT; i++) {
        uint32_t temp = 0;
        if (sddf_thermal_get_temp(thermal_channel, i, &temp) == 0) {
            sddf_printf_("Current temperature on sensor%d: %d.%d°C\n", i, temp / 1000,
                         (temp % 1000 - temp % 100) / 100);
        }

        sddf_thermal_set_alarm(thermal_channel, i, ALERM_TEMP);
    }

    sddf_pwm_fan_speed(pwm_channel, Low);
}

void notified(sddf_channel ch)
{
    sddf_printf_("Received high temperature alarm\n");
    sddf_pwm_fan_speed(pwm_channel, Full);
}