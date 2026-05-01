#pragma once

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <stdbool.h>
#include <stdint.h>
#include "include/gpio_common/gpio_common.h"

/* Timer States for TRIG pin */ 
#define TRIG_UNSET (0)
#define TRIG_HIGH (1)
#define TRIG_LOW (2)

/* Time (ms) Timeout for Sensor Read */
#define SENSOR_TIMEOUT (38)

/* Client-side Ultrasonic Functions */
uint64_t get_ultrasonic_reading(int echo_ch, int trigger_ch);
void sensor_init(int echo_ch, int trigger_ch);
