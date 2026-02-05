#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>
#include "gpio_config.h"
#include <sddf/gpio/meson/gpio.h>

#define GPIO_HIGH (1)
#define GPIO_LOW (0)

void gpio_init(int gpio_ch, int direction);
void digital_write(int gpio_ch, int value);