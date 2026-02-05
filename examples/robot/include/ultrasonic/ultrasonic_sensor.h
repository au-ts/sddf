#pragma once

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <stdbool.h>
#include <stdint.h>

/* Ultrasonic GPIO Channels */
#define GPIO_CHANNEL_ECHO (3)
#define GPIO_CHANNEL_TRIG (4)

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

/* Timer States for TRIG pin */ 
#define TRIG_UNSET (0)
#define TRIG_HIGH (1)
#define TRIG_LOW (2)

/* Time (ms) Timeout for Sensor Read */
#define SENSOR_TIMEOUT (38)

/* Client-side Ultrasonic Functions */
uint64_t get_ultrasonic_reading();
void sensor_init(void);