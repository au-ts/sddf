#pragma once

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <stdbool.h>
#include <stdint.h>
#include "include/gpio_common/gpio_common.h"

/* Client-side Ultrasonic Functions */
void detect_encoder_rising_edge(int gpio_ch_a, int gpio_ch_b);
void encoder_init(int gpio_ch_a, int gpio_ch_b);
