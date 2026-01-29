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
#include "gpio.h"

/* because start is not page aligned */
#define GPIO_REGS_BASE_ADDRESS_OFFSET           0x400
#define GPIO_AO_REGS_BASE_ADDRESS_OFFSET        0x0
#define IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET    0x0

/*
================================================================================
=============================  GPIO REGISTERS ==================================
================================================================================
*/

// GPIOZ ( 0 - 15 pins ) | reg4
#define PAD_PULL_UP_REG4          0x3e
#define PAD_PULL_UP_EN_REG4       0x4c
#define PREG_PAD_GPIO4_I          0x1e
#define PREG_PAD_GPIO4_O          0x1d
#define PREG_PAD_GPIO4_EN_N       0x1c
#define PAD_DS_REG4A              0xd5

// GPIOA ( 0 - 15 pins ) | reg5
#define PAD_PULL_UP_REG5          0x3f
#define PAD_PULL_UP_EN_REG5       0x4d
#define PREG_PAD_GPIO5_I          0x22
#define PREG_PAD_GPIO5_O          0x21
#define PREG_PAD_GPIO5_EN_N       0x20
#define PAD_DS_REG5A              0xd6

// BOOT ( 0 - 15 pins ) | reg0
#define PAD_PULL_UP_REG0          0x3a
#define PAD_PULL_UP_EN_REG0       0x48
#define PREG_PAD_GPIO0_I          0x12
#define PREG_PAD_GPIO0_O          0x11
#define PREG_PAD_GPIO0_EN_N       0x10
#define PAD_DS_REG0A              0xd0

// GPIOC ( 0 - 7 pins ) | reg1
#define PAD_PULL_UP_REG1          0x3b
#define PAD_PULL_UP_EN_REG1       0x49
#define PREG_PAD_GPIO1_I          0x15
#define PREG_PAD_GPIO1_O          0x14
#define PREG_PAD_GPIO1_EN_N       0x13
#define PAD_DS_REG1A              0xd1

// GPIOX ( 0 - 19 pins ) | reg2
#define PAD_PULL_UP_REG2          0x3c
#define PAD_PULL_UP_EN_REG2       0x4a
#define PREG_PAD_GPIO2_I          0x18
#define PREG_PAD_GPIO2_O          0x17
#define PREG_PAD_GPIO2_EN_N       0x16
#define PAD_DS_REG2A              0xd2
#define PAD_DS_REG2B              0xd3

// GPIOH ( 0 - 8 pins ) | reg3
#define PAD_PULL_UP_REG3          0x3d
#define PAD_PULL_UP_EN_REG3       0x4b
#define PREG_PAD_GPIO3_I          0x1b
#define PREG_PAD_GPIO3_O          0x1a
#define PREG_PAD_GPIO3_EN_N       0x19
#define PAD_DS_REG3A              0xd4

// GPIOAO ( 0 - 11 pins ) and GPIOE ( 0 - 2 pins ) and TEST_N (0 - 0 pin)
#define AO_RTI_PULL_UP_REG        0x0b
#define AO_RTI_PULL_UP_EN_REG     0x0c
#define AO_GPIO_I                 0x0a
#define AO_GPIO_O                 0x0d
#define AO_GPIO_O_EN_N            0x09
#define AO_PAD_DS_A               0x07
#define AO_PAD_DS_B               0x08

/*
================================================================================
================================  IRQ REGISTERS  ===============================
================================================================================
*/

/* Contains all functionality fields present in the other Registers
   Its just specfic to the ao_gpio_irq0 and ao_gpio_irq1 */
#define AO_IRQ_GPIO_REG                   0x0021

/* For gpio_irq[0-7] */
#define GPIO_INTERUPT_EDGE_AND_POLARITY   0x3c20
#define GPIO_0_3_PIN_SELECT               0x3c21
#define GPIO_4_7_PIN_SELECT               0x3c22
#define GPIO_FILTER_SELECT                0x3c23

/*
================================================================================
================================  DATA STRUCTURES  =============================
================================================================================
*/

typedef enum {
	MESON_GPIO_REG_PULLEN = 0,
	MESON_GPIO_REG_PULL,
	MESON_GPIO_REG_DIR,
	MESON_GPIO_REG_OUT,
	MESON_GPIO_REG_IN,
	MESON_GPIO_REG_DS,
	MESON_GPIO_FUNC_COUNT,
} meson_gpio_reg_type_t;

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
 * @register_offset:	   hardware offset from above
 * @start_bit:	         starting bit in the register (inclusive)
 * @end_bit:	         last bit in the register (inclusive)
 * @start_pin_number:	what pin number in the gpio bank is mapped to the starting bit
 * @is_last:	         if this is the last meson_gpio_register_data struct in containing structs array
 */
struct meson_gpio_register_data {
   uint32_t register_offset;
   uint32_t start_bit;
   uint32_t end_bit;
   uint32_t start_pin_number;
   bool is_last;
};

struct meson_gpio_bank {
   meson_gpio_bank_t bank;
   const struct meson_gpio_register_data *registers;
};

struct meson_gpio_function {
   meson_gpio_reg_type_t function;
   const struct meson_gpio_bank *banks;
};

static const struct meson_gpio_function gpio_config_control[] = {
   {
      .function = MESON_GPIO_REG_PULLEN,
      .banks = (const struct meson_gpio_bank[]){
         { .bank = MESON_GPIO_AO, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_RTI_PULL_UP_EN_REG, .start_bit = 0, .end_bit = 11, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_Z, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_EN_REG4, .start_bit = 0, .end_bit = 13, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_H, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_EN_REG3, .start_bit = 4, .end_bit = 7, .start_pin_number = 4, .is_last = true }
         }},
         { .bank = MESON_GPIO_BOOT, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_EN_REG0, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_C, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_EN_REG1, .start_bit = 0, .end_bit = 6, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_A, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_EN_REG5, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_X, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_EN_REG2, .start_bit = 0, .end_bit = 19, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_E, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_RTI_PULL_UP_EN_REG, .start_bit = 16, .end_bit = 18, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_TEST_N, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_RTI_PULL_UP_EN_REG, .start_bit = 31, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
      }
   },
   {
      .function = MESON_GPIO_REG_PULL,
      .banks = (const struct meson_gpio_bank[]){
         { .bank = MESON_GPIO_AO, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_RTI_PULL_UP_REG, .start_bit = 0, .end_bit = 11, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_Z, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_REG4, .start_bit = 0, .end_bit = 13, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_H, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_REG3, .start_bit = 4, .end_bit = 7, .start_pin_number = 4, .is_last = true }
         }},
         { .bank = MESON_GPIO_BOOT, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_REG0, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_C, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_REG1, .start_bit = 0, .end_bit = 6, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_A, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_REG5, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_X, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_PULL_UP_REG2, .start_bit = 0, .end_bit = 19, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_E, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_RTI_PULL_UP_REG, .start_bit = 16, .end_bit = 18, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_TEST_N, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_RTI_PULL_UP_REG, .start_bit = 31, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
      }
   },
   {
      .function = MESON_GPIO_REG_DIR,
      .banks = (const struct meson_gpio_bank[]){
         { .bank = MESON_GPIO_AO, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_O_EN_N, .start_bit = 0, .end_bit = 11, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_Z, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO4_EN_N, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_H, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO3_EN_N, .start_bit = 0, .end_bit = 8, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_BOOT, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO0_EN_N, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_C, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO1_EN_N, .start_bit = 0, .end_bit = 7, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_A, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO5_EN_N, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_X, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO2_EN_N, .start_bit = 0, .end_bit = 19, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_E, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_O_EN_N, .start_bit = 16, .end_bit = 18, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_TEST_N, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_O_EN_N, .start_bit = 31, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
      }
   },
   {
      .function = MESON_GPIO_REG_OUT,
      .banks = (const struct meson_gpio_bank[]){
         { .bank = MESON_GPIO_AO, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_O, .start_bit = 0, .end_bit = 11, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_Z, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO4_O, .start_bit = 0, .end_bit = 13, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_H, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO3_O, .start_bit = 4, .end_bit = 7, .start_pin_number = 4, .is_last = true }
         }},
         { .bank = MESON_GPIO_BOOT, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO0_O, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_C, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO1_O, .start_bit = 0, .end_bit = 6, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_A, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO5_O, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_X, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO2_O, .start_bit = 0, .end_bit = 19, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_E, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_O, .start_bit = 16, .end_bit = 18, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_TEST_N, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_O, .start_bit = 31, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
      }
   },
   {
      .function = MESON_GPIO_REG_IN,
      .banks = (const struct meson_gpio_bank[]){
         { .bank = MESON_GPIO_AO, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_I, .start_bit = 0, .end_bit = 11, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_Z, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO4_I, .start_bit = 0, .end_bit = 13, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_H, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO3_I, .start_bit = 0, .end_bit = 8, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_BOOT, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO0_I, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_C, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO1_I, .start_bit = 0, .end_bit = 7, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_A, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO5_I, .start_bit = 0, .end_bit = 15, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_X, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PREG_PAD_GPIO2_I, .start_bit = 0, .end_bit = 19, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_E, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_I, .start_bit = 16, .end_bit = 18, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_TEST_N, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_GPIO_I, .start_bit = 31, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
      }
   },
   {
      .function = MESON_GPIO_REG_DS,
      .banks = (const struct meson_gpio_bank[]){
         { .bank = MESON_GPIO_AO, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_PAD_DS_A, .start_bit = 0, .end_bit = 23, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_Z, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_DS_REG4A, .start_bit = 0, .end_bit = 27, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_H, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_DS_REG3A, .start_bit = 8, .end_bit = 15, .start_pin_number = 4, .is_last = true }
         }},
         { .bank = MESON_GPIO_BOOT, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_DS_REG0A, .start_bit = 0, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_C, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_DS_REG1A, .start_bit = 0, .end_bit = 13, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_A, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_DS_REG5A, .start_bit = 0, .end_bit = 31, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_X, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = PAD_DS_REG2A, .start_bit = 0, .end_bit = 31, .start_pin_number = 0, .is_last = false },
               { .register_offset = PAD_DS_REG2B, .start_bit = 0, .end_bit = 5, .start_pin_number = 16, .is_last = false },
               { .register_offset = PAD_DS_REG2B, .start_bit = 4, .end_bit = 5, .start_pin_number = 19, .is_last = true }  // pin 18 and 19 share the same bit
         }},
         { .bank = MESON_GPIO_E, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_PAD_DS_B, .start_bit = 0, .end_bit = 5, .start_pin_number = 0, .is_last = true }
         }},
         { .bank = MESON_GPIO_TEST_N, .registers = (const struct meson_gpio_register_data[]){
               { .register_offset = AO_PAD_DS_B, .start_bit = 28, .end_bit = 29, .start_pin_number = 0, .is_last = true }
         }},
      }
   }
};

typedef enum {
	MESON_IRQ_REG_BOTHEDGEEN = 0,
	MESON_IRQ_REG_EDGE,
      MESON_IRQ_REG_POL,
	MESON_IRQ_REG_FIL,
	MESON_IRQ_REG_AOSEL,
      MESON_IRQ_REG_SEL,
	MESON_IRQ_FUNC_COUNT,
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
 * @register_offset:	   hardware offset from above
 * @start_bit:	         starting bit in the register (inclusive)
 * @end_bit:	         last bit in the register (inclusive)
 * @start_irq_number:	what channel number out of the channels is mapped to the starting bit
 * @is_last:	         if this is the last meson_irq_register_data struct in containing structs array
 */
struct meson_irq_register_data {
   uint32_t register_offset;
   uint32_t start_bit;
   uint32_t end_bit;
   uint32_t start_irq_number;
   bool is_last;
};

struct meson_irq_function {
   meson_irq_reg_type_t function;
   const struct meson_irq_register_data *registers;
};

static const struct meson_irq_function irq_config_control[] = {
   {
      .function = MESON_IRQ_REG_BOTHEDGEEN,
      .registers = (const struct meson_irq_register_data[]){
         { .register_offset = GPIO_INTERUPT_EDGE_AND_POLARITY, .start_bit = 24, .end_bit = 31, .start_irq_number = MESON_GPIO_IRQ_0, .is_last = false },
         { .register_offset = AO_IRQ_GPIO_REG, .start_bit = 20, .end_bit = 21, .start_irq_number = MESON_GPIO_AO_IRQ_0, .is_last = true }
      }
   },
   {
      .function = MESON_IRQ_REG_EDGE,
      .registers = (const struct meson_irq_register_data[]){
         { .register_offset = GPIO_INTERUPT_EDGE_AND_POLARITY, .start_bit = 0, .end_bit = 7, .start_irq_number = MESON_GPIO_IRQ_0, .is_last = false },
         { .register_offset = AO_IRQ_GPIO_REG, .start_bit = 18, .end_bit = 19, .start_irq_number = MESON_GPIO_AO_IRQ_0, .is_last = true }
      }
   },
   {
      .function = MESON_IRQ_REG_POL,
      .registers = (const struct meson_irq_register_data[]){
         { .register_offset = GPIO_INTERUPT_EDGE_AND_POLARITY, .start_bit = 16, .end_bit = 23, .start_irq_number = MESON_GPIO_IRQ_0, .is_last = false },
         { .register_offset = AO_IRQ_GPIO_REG, .start_bit = 16, .end_bit = 17, .start_irq_number = MESON_GPIO_AO_IRQ_0, .is_last = true }
      }
   },
   {
      .function = MESON_IRQ_REG_FIL,
      .registers = (const struct meson_irq_register_data[]){
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 0, .end_bit = 2, .start_irq_number = MESON_GPIO_IRQ_0, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 4, .end_bit = 6, .start_irq_number = MESON_GPIO_IRQ_1, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 8, .end_bit = 10, .start_irq_number = MESON_GPIO_IRQ_2, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 12, .end_bit = 14, .start_irq_number = MESON_GPIO_IRQ_3, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 16, .end_bit = 18, .start_irq_number = MESON_GPIO_IRQ_4, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 20, .end_bit = 22, .start_irq_number = MESON_GPIO_IRQ_5, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 24, .end_bit = 26, .start_irq_number = MESON_GPIO_IRQ_6, .is_last = false },
         { .register_offset = GPIO_FILTER_SELECT, .start_bit = 28, .end_bit = 30, .start_irq_number = MESON_GPIO_IRQ_7, .is_last = false },
         { .register_offset = AO_IRQ_GPIO_REG, .start_bit = 8, .end_bit = 10, .start_irq_number = MESON_GPIO_AO_IRQ_0, .is_last = false },
         { .register_offset = AO_IRQ_GPIO_REG, .start_bit = 12, .end_bit = 14, .start_irq_number = MESON_GPIO_AO_IRQ_1, .is_last = true },
      }
   },
   {
      .function = MESON_IRQ_REG_AOSEL,
      .registers = (const struct meson_irq_register_data[]){
         { .register_offset = AO_IRQ_GPIO_REG, .start_bit = 0, .end_bit = 7, .start_irq_number = MESON_GPIO_AO_IRQ_0, .is_last = true }
      }
   },
   {
      .function = MESON_IRQ_REG_SEL,
      .registers = (const struct meson_irq_register_data[]){
         { .register_offset = GPIO_0_3_PIN_SELECT, .start_bit = 0, .end_bit = 31, .start_irq_number = MESON_GPIO_IRQ_0, .is_last = false },
         { .register_offset = GPIO_4_7_PIN_SELECT, .start_bit = 0, .end_bit = 31, .start_irq_number = MESON_GPIO_IRQ_4, .is_last = true }
      }
   }
};
