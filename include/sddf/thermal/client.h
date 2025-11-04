/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <os/sddf.h>

typedef enum {
    SENSOR_LOCATION_CPU = 0,
    SENSOR_LOCATION_GPU = 1,
    // Add more possible locations of the sensor
} SensorLocation;

typedef enum {
    THERMAL_NOERROR = 0,
    THERMAL_EINVAL = 1,
    // Add more possible locations of the sensor
} thermal_error_t;

typedef struct {
    uint32_t sensor_index;
    SensorLocation location;
} SensorInfoEntry;

#ifdef CONFIG_PLAT_ROCKPRO64
const SensorInfoEntry SENSOR_INFO[] = {
    {
        .sensor_index = 0,
        .location = SENSOR_LOCATION_CPU,
    },
    {
        .sensor_index = 1,
        .location = SENSOR_LOCATION_GPU,
    }
};

const uint32_t SENSOR_COUNT = sizeof(CHANNEL_INFO) / sizeof(SensorInfoEntry);
#endif

#define SDDF_THERMAL_GET_TEMPERATURE 0
#define SDDF_THERMAL_SET_ALARM_TEMPERATURE 1

static inline int32_t sddf_thermal_get_temp(unsigned int channel, uint32_t sensor_index, uint32_t *temp)
{
    sddf_set_mr(0, sensor_index);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_THERMAL_GET_TEMPERATURE, 0, 0, 1));
    uint32_t error = sddf_get_mr(0);
    if (!error) {
        *temp = sddf_get_mr(1);
    }
    return error;
}

static inline uint32_t sddf_thermal_set_alarm(unsigned int channel, uint32_t sensor_index, int32_t temp)
{
    sddf_set_mr(0, sensor_index);
    sddf_set_mr(1, temp);
    sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_THERMAL_SET_ALARM_TEMPERATURE, 0, 0, 2));
    return sddf_get_mr(0);
}