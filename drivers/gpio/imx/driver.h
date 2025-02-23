/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Made by Tristan Clinton-Muehr

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>
#include <sddf/gpio/meson/gpio.h>

/*
================================================================================
=============================  GPIO REGISTERS ==================================
================================================================================
*/

// GPIO1_IO00 - GPIO1_IO29 (0 - 29 pins)
#define GPIO1_DR        0x0
#define GPIO1_GDIR      0x4
#define GPIO1_PSR       0x8

// GPIO2_IO00 - GPIO2_IO20 (0 - 20 pins)
#define GPIO2_DR        0x0
#define GPIO2_GDIR      0x4
#define GPIO2_PSR       0x8

// GPIO3_IO00 - GPIO3_IO25 (0 - 25 pins)
#define GPIO3_DR        0x0
#define GPIO3_GDIR      0x4
#define GPIO3_PSR       0x8

// GPIO4_IO00 - GPIO4_IO31 (0 - 31 pins)
#define GPIO4_DR        0x0
#define GPIO4_GDIR      0x4
#define GPIO4_PSR       0x8

// GPIO5_IO00 - GPIO5_IO29 (0 - 29 pins)
#define GPIO5_DR        0x0
#define GPIO5_GDIR      0x4
#define GPIO5_PSR       0x8

/*
================================================================================
================================  IRQ REGISTERS  ===============================
================================================================================
*/

#define GPIO1_ICR1          0xC
#define GPIO1_ICR2          0x10
#define GPIO1_IMR           0x14
#define GPIO1_ISR           0x18
#define GPIO1_EDGE_SEL      0x1C

#define GPIO2_ICR1          0xC
#define GPIO2_ICR2          0x10
#define GPIO2_IMR           0x14
#define GPIO2_ISR           0x18
#define GPIO2_EDGE_SEL      0x1C

#define GPIO3_ICR1          0xC
#define GPIO3_ICR2          0x10
#define GPIO3_IMR           0x14
#define GPIO3_ISR           0x18
#define GPIO3_EDGE_SEL      0x1C

#define GPIO4_ICR1          0xC
#define GPIO4_ICR2          0x10
#define GPIO4_IMR           0x14
#define GPIO4_ISR           0x18
#define GPIO4_EDGE_SEL      0x1C

#define GPIO5_ICR1          0xC
#define GPIO5_ICR2          0x10
#define GPIO5_IMR           0x14
#define GPIO5_ISR           0x18
#define GPIO5_EDGE_SEL      0x1C

/*
================================================================================
==========================  GPIO EXTRA FUNC REGISTERS  =========================
================================================================================
*/

/*
================================================================================
================================  DATA STRUCTURES  =============================
================================================================================
*/

typedef enum {
	IMX_GPIO_REG_DR = 0,
	IMX_GPIO_REG_GDIR,
    IMX_GPIO_REG_PSR,
	IMX_GPIO_FUNC_COUNT,
} imx_gpio_reg_type_t;

struct imx_gpio_instance {
   imx_gpio_instance_t instance;
   uint32_t register_offset;
};

struct meson_gpio_function {
   meson_gpio_reg_type_t function;
   const struct imx_gpio_instance *instances;
};

static const struct imx_gpio_function gpio_config_control[] = {
    {
        .function = IMX_GPIO_REG_DR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .register_offset = GPIO1_DR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .register_offset = GPIO2_DR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .register_offset = GPIO3_DR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .register_offset = GPIO4_DR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .register_offset = GPIO5_DR },
        }
    },
    {
        .function = IMX_GPIO_REG_GDIR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .register_offset = GPIO1_GDIR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .register_offset = GPIO2_GDIR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .register_offset = GPIO3_GDIR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .register_offset = GPIO4_GDIR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .register_offset = GPIO5_GDIR },
        }
    },
    {
        .function = IMX_GPIO_REG_PSR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .register_offset = GPIO1_PSR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .register_offset = GPIO2_PSR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .register_offset = GPIO3_PSR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .register_offset = GPIO4_PSR },
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .register_offset = GPIO5_PSR },
        }
   }
}

