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
==========================  GPIO AND IRQ REGISTERS =============================
================================================================================
*/

// GPIO1_IO00 - GPIO1_IO29 (0 - 29 pins)
#define GPIO1_DR            0x0
#define GPIO1_GDIR          0x4
#define GPIO1_PSR           0x8
#define GPIO1_ICR1          0xC
#define GPIO1_ICR2          0x10
#define GPIO1_IMR           0x14
#define GPIO1_ISR           0x18
#define GPIO1_EDGE_SEL      0x1C

// GPIO2_IO00 - GPIO2_IO20 (0 - 20 pins)
#define GPIO2_DR            0x0
#define GPIO2_GDIR          0x4
#define GPIO2_PSR           0x8
#define GPIO2_ICR1          0xC
#define GPIO2_ICR2          0x10
#define GPIO2_IMR           0x14
#define GPIO2_ISR           0x18
#define GPIO2_EDGE_SEL      0x1C

// GPIO3_IO00 - GPIO3_IO25 (0 - 25 pins)
#define GPIO3_DR            0x0
#define GPIO3_GDIR          0x4
#define GPIO3_PSR           0x8
#define GPIO3_ICR1          0xC
#define GPIO3_ICR2          0x10
#define GPIO3_IMR           0x14
#define GPIO3_ISR           0x18
#define GPIO3_EDGE_SEL      0x1C

// GPIO4_IO00 - GPIO4_IO31 (0 - 31 pins)
#define GPIO4_DR            0x0
#define GPIO4_GDIR          0x4
#define GPIO4_PSR           0x8
#define GPIO4_ICR1          0xC
#define GPIO4_ICR2          0x10
#define GPIO4_IMR           0x14
#define GPIO4_ISR           0x18
#define GPIO4_EDGE_SEL      0x1C

// GPIO5_IO00 - GPIO5_IO29 (0 - 29 pins)
#define GPIO5_DR            0x0
#define GPIO5_GDIR          0x4
#define GPIO5_PSR           0x8
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
    IMX_IRQ_REG_IMR,
    IMX_IRQ_EDGE_SEL,
    IMX_IRQ_ICR,
    IMX_IRQ_ISR,
	IMX_GPIO_AND_IRQ_FUNC_COUNT,
} imx_gpio_and_irq_reg_type_t;

static const uint32_t imx_gpio_and_irq_bit_strides[] = {
    1 /* IMX_GPIO_REG_DR */,
    1 /* IMX_GPIO_REG_GDIR */,
    1 /* IMX_GPIO_REG_PSR */,
    1 /* IMX_IRQ_REG_IMR */,
    1 /* IMX_IRQ_EDGE_SEL */,
    2 /* IMX_IRQ_ICR */,
    1 /* IMX_IRQ_ISR */
};

/**
 * struct imx_gpio_and_irq_register_data - a register and its metadata
 *
 * @register_offset:	   hardware offset from above
 * @start_pin_number:	   what pin number in the gpio bank is mapped to the starting bit
 * @is_last:	           if this is the last imx_gpio_and_irq_register_data struct in containing structs array
 */
struct imx_gpio_and_irq_register_data {
    uint32_t register_offset;
    uint32_t start_pin_number;
    bool is_last;
};

struct imx_gpio_instance {
   imx_gpio_instance_t instance;
   const struct imx_gpio_and_irq_register_data *registers;
};

struct imx_gpio_function {
   imx_gpio_reg_type_t function;
   const struct imx_gpio_instance *instances;
};

static const struct imx_gpio_function gpio_and_irq_config_control[] = {
    {
        .function = IMX_GPIO_REG_DR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_DR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_DR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_DR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_DR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_DR, .start_pin_number = 0, .is_last = true }
            }},
        }
    },
    {
        .function = IMX_GPIO_REG_GDIR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_GDIR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_GDIR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_GDIR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_GDIR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_GDIR, .start_pin_number = 0, .is_last = true }
            }},
        }
    },
    {
        .function = IMX_GPIO_REG_PSR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_PSR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_PSR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_PSR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_PSR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_PSR, .start_pin_number = 0, .is_last = true }
            }},
        }
    },
    {
        .function = IMX_IRQ_REG_IMR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_IMR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_IMR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_IMR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_IMR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_IMR, .start_pin_number = 0, .is_last = true }
            }},
        }
    },
    {
        .function = IMX_IRQ_EDGE_SEL,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_EDGE_SEL, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_EDGE_SEL, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_EDGE_SEL, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_EDGE_SEL, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_EDGE_SEL, .start_pin_number = 0, .is_last = true }
            }},
        }
    },
    {
        .function = IMX_IRQ_ICR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_ICR1, .start_pin_number = 0, .is_last = false },
                { .register_offset = GPIO1_ICR2, .start_pin_number = 16, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_ICR1, .start_pin_number = 0, .is_last = false },
                { .register_offset = GPIO2_ICR2, .start_pin_number = 16, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_ICR1, .start_pin_number = 0, .is_last = false },
                { .register_offset = GPIO3_ICR2, .start_pin_number = 16, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_ICR1, .start_pin_number = 0, .is_last = false },
                { .register_offset = GPIO4_ICR2, .start_pin_number = 16, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_ICR1, .start_pin_number = 0, .is_last = false },
                { .register_offset = GPIO5_ICR2, .start_pin_number = 16, .is_last = true }
            }},
        }
    },
    {
        .function = IMX_IRQ_ISR,
        .instances = (const struct imx_gpio_instance[]){
            { .instance = IMX_GPIO_INSTANCE_GPIO_1, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO1_ISR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_2, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO2_ISR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_3, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO3_ISR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_4, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO4_ISR, .start_pin_number = 0, .is_last = true }
            }},
            { .instance = IMX_GPIO_INSTANCE_GPIO_5, .registers = (const struct imx_gpio_and_irq_register_data[]){
                { .register_offset = GPIO5_ISR, .start_pin_number = 0, .is_last = true }
            }},
        }
    },
}
