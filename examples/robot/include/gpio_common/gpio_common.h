#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/gpio/protocol.h>
#include "include/gpio_common/gpio_config.h"


#define GPIO_HIGH (1)
#define GPIO_LOW (0)

#define GPIO_DIRECTION_INPUT (0)
#define GPIO_DIRECTION_OUTPUT (1)

void gpio_init(int gpio_ch, int direction);
void digital_write(int gpio_ch, int value);
int digital_read(int gpio_ch);