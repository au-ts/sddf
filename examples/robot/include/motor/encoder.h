#pragma once

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <stdbool.h>
#include <stdint.h>
#include "include/gpio_common/gpio_common.h"

/* Ultrasonic GPIO Channels */
#define GPIO_CHANNEL_ECHO (3)
#define GPIO_CHANNEL_TRIG (4)

/* Client-side Ultrasonic Functions */
uint64_t get_encoder_reading(int gpio_ch_a, int gpio_ch_b);
void encoder_init(int gpio_ch_a, int gpio_ch_b);
