/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

#ifndef GPIO_DRIVER_H
#define GPIO_DRIVER_H

#define GPIO_REGS_OFFSET 1024

/*
================================================================================
=============================  GPIO REGISTERS ==================================
================================================================================
*/

// GPIOZ ( 0 - 15 pins ) // reg4
#define PAD_PULL_UP_REG4          0x3e
#define PAD_PULL_UP_EN_REG4       0x4c
#define PREG_PAD_GPIO4_I          0x1e
#define PREG_PAD_GPIO4_O          0x1d
#define PREG_PAD_GPIO4_EN_N       0x1c
#define PAD_DS_REG4A              0xd5

// GPIOA ( 0 - 15 pins ) // reg5
#define PAD_PULL_UP_REG5          0x3f
#define PAD_PULL_UP_EN_REG5       0x4d
#define PREG_PAD_GPIO5_I          0x22
#define PREG_PAD_GPIO5_O          0x21
#define PREG_PAD_GPIO5_EN_N       0x20
#define PAD_DS_REG5A              0xd6

// BOOT ( 0 - 15 pins ) // reg0
#define PAD_PULL_UP_REG0          0x3a
#define PAD_PULL_UP_EN_REG0       0x48
#define PREG_PAD_GPIO0_I          0x12
#define PREG_PAD_GPIO0_O          0x11
#define PREG_PAD_GPIO0_EN_N       0x10
#define PAD_DS_REG0A              0xd0

// GPIOC ( 0 - 7 pins ) // reg1
#define PAD_PULL_UP_REG1          0x3b
#define PAD_PULL_UP_EN_REG1       0x49
#define PREG_PAD_GPIO1_I          0x15
#define PREG_PAD_GPIO1_O          0x14
#define PREG_PAD_GPIO1_EN_N       0x13
#define PAD_DS_REG1A              0xd1

// GPIOX ( 0 - 19 pins ) // reg2
#define PAD_PULL_UP_REG2          0x3c
#define PAD_PULL_UP_EN_REG2       0x4a
#define PREG_PAD_GPIO2_I          0x18
#define PREG_PAD_GPIO2_O          0x17
#define PREG_PAD_GPIO2_EN_N       0x16
#define PAD_DS_REG2A              0xd2
#define PAD_DS_REG2B              0xd3

// GPIOH ( 0 - 8 pins ) // reg3
#define PAD_PULL_UP_REG3          0x3d
#define PAD_PULL_UP_EN_REG3       0x4b
#define PREG_PAD_GPIO3_I          0x1b
#define PREG_PAD_GPIO3_O          0x1a
#define PREG_PAD_GPIO3_EN_N       0x19
#define PAD_DS_REG3A              0xd4

/* Always on */

// GPIOAO ( 0 - 11 pins ) and  GPIOE ( 0 - 2 pins ) and TEST_N (0 - 0 pin)
#define AO_RTI_PULL_UP_REG        0x0b
#define AO_RTI_PULL_UP_EN_REG     0x0c
#define AO_GPIO_I                 0x0a
#define AO_GPIO_O                 0x0d
#define AO_GPIO_O_EN_N            0x09
#define AO_PAD_DS_A               0x07
#define AO_PAD_DS_B               0x08

/* lock above AO registers */
// #define AO_PINMUX_LOCK            0x17 - not implemented

/*
================================================================================
================================  IRQ CONTROL  =================================
================================================================================
*/

/* Contains all functionality fields present in the other Registers
   Its just specfic to the ao_gpio_irq0 and ao_gpio_irq1 */
#define AO_IRQ_GPIO_REG 0x21

/* For gpio_irq[0-7] */
#define GPIO_INTERUPT_EDGE_AND_POLARITY 0x3c20
#define GPIO_0_3_PIN_SELECT 0x3c21
#define GPIO_4_7_PIN_SELECT 0x3c22
#define GPIO_FILTER_SELECT 0x3c23

// for select gpio to a pin that doesnt match anything
#define UNASSIGNED_IRQ_GPIO_PIN_VALUE 0

/*
================================================================================
*/

#define MESON_MAX_GPIO_REGISTERS_DATA 3

typedef enum {
	MESON_GPIO_REG_PULLEN = 0,
	MESON_GPIO_REG_PULL,
	MESON_GPIO_REG_DIR,
	MESON_GPIO_REG_OUT,
	MESON_GPIO_REG_IN,
	MESON_GPIO_REG_DS,
	MESON_GPIO_NUM_REG, // not actually a register - just a count
} meson_gpio_reg_type_t;

/* how many bits are assigned for each register type per pin */
static const uint32_t meson_gpio_bit_strides[] = {
	1 /* MESON_GPIO_REG_PULLEN */,
    1 /* MESON_GPIO_REG_PULL */,
    1 /* MESON_GPIO_REG_DIR */,
    1 /* MESON_GPIO_REG_OUT */,
    1 /* MESON_GPIO_REG_IN */,
    2 /* MESON_GPIO_REG_DS */
};

/**
 * struct meson_gpio_register_data - a register and its metadata
 *
 * @register_offset:	hardware offset from above
 * @start_bit:	        starting bit in the register (inclusive)
 * @end_bit:	        last bit in the register (inclusive)
 * @start_pin_number:	what pin number in the gpio bank is mapped to the starting bit
 * @is_last:	        if this is the last meson_register_data struct in meson_gpio_bank registers array
 */
struct meson_gpio_register_data {
    uint32_t register_offset;
    uint32_t start_bit;
    uint32_t end_bit;
    uint32_t start_pin_number;
    bool is_last;
};

/**
 * struct meson_gpio_bank - contains all registers for its designated function
 *
 * @bank:	            meson_gpio_bank_t
 * @registers:          array of meson_gpio_register_data's | driver assumes these are in order of ascending pin number
 */
struct meson_gpio_bank {
    int bank;
    struct meson_gpio_register_data registers[MESON_MAX_GPIO_REGISTERS_DATA];
};

#define MESON_GPIO_REGISTER_DATA(reg_offset, s_bit, e_bit, s_pin, last)    \
    (struct meson_gpio_register_data) {                               \
        .register_offset = reg_offset,                                \
        .start_bit = s_bit,                                           \
        .end_bit = e_bit,                                             \
        .start_pin_number = s_pin,                                    \
        .is_last = last                                               \
    }

#define MESON_GPIO_BANK(bank_id, ...)                                 \
    {                                                                 \
        .bank = bank_id,                                              \
        .registers = { __VA_ARGS__ }                                  \
    }

/*
================================================================================
*/

#define MESON_MAX_IRQ_REGISTERS_DATA 10

typedef enum {
	MESON_IRQ_REG_BOTHEDGEEN = 0,
	MESON_IRQ_REG_EDGE,
    MESON_IRQ_REG_POL,
	MESON_IRQ_REG_FIL,
	MESON_IRQ_REG_AOSEL,
    MESON_IRQ_REG_SEL,
    // MESON_IRQ_REG_FILCLKEN - not implemented
	MESON_IRQ_NUM_REG, // just a count
} meson_irq_reg_type_t;

/* how many bits are assigned for each register type per pin */
static const uint32_t meson_irq_bit_strides[] = {
	1 /* MESON_IRQ_REG_BOTHEDGEEN */,
    1 /* MESON_IRQ_REG_EDGE */,
    1 /* MESON_IRQ_REG_POL */,
    3 /* MESON_IRQ_REG_FIL */,
    4 /* MESON_IRQ_REG_AOSEL */,
    8 /* MESON_IRQ_REG_SEL */
};

/**
 * struct meson_irq_register_data - a register and its metadata
 *
 * @register_offset:	    hardware offset from above
 * @start_bit:	            starting bit in the register (inclusive)
 * @end_bit:	            last bit in the register (inclusive)
 * @start_channel_number:	what channel number is mapped to the starting bit
 * @is_last:	            if this is the last meson_irq_register_data struct in in the irq function array
 */
struct meson_irq_register_data {
    uint32_t register_offset;
    uint32_t start_bit;
    uint32_t end_bit;
    uint32_t start_channel_number;
    bool is_last;
};

#define MESON_IRQ_REGISTER_DATA(reg_offset, s_bit, e_bit, s_ch, last)    \
    {                                                                    \
        .register_offset = reg_offset,                                   \
        .start_bit = s_bit,                                              \
        .end_bit = e_bit,                                                \
        .start_channel_number = s_ch,                                    \
        .is_last = last                                                  \
    }

/*
================================================================================
*/

#endif
