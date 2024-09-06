// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause

// Document referenced: Chapter 7.9 of Amlogic S905X3 Datasheet revision 02.

// Unlike odroidc4.py, this file simply define the default pinmux values

#include <stdint.h>

// Even though these default values are set during a watchdog event,
// it is better to set them up again to remove u-boot's initialisation effort so that
// our driver can be properly tested.

#define MUX_REG_ADDR(base, offset) ((uint32_t *) base + (offset * 4))

typedef struct {
    uint32_t offset;
    uint32_t value;
} pindata_t;

// The "Always-On" domain pinmux can't be reset as that would halt the kernel.

// Peripherals domain:

// Muxing registers, connect this pad to what port
#define PERIPHS_PIN_MUX_0_OFFSET   0xB0
#define PERIPHS_PIN_MUX_1_OFFSET   0xB1
#define PERIPHS_PIN_MUX_2_OFFSET   0xB2
#define PERIPHS_PIN_MUX_3_OFFSET   0xB3
#define PERIPHS_PIN_MUX_4_OFFSET   0xB4
#define PERIPHS_PIN_MUX_5_OFFSET   0xB5
#define PERIPHS_PIN_MUX_6_OFFSET   0xB6
#define PERIPHS_PIN_MUX_7_OFFSET   0xB7
#define PERIPHS_PIN_MUX_8_OFFSET   0xB8
#define PERIPHS_PIN_MUX_9_OFFSET   0xB9
#define PERIPHS_PIN_MUX_A_OFFSET   0xBA
#define PERIPHS_PIN_MUX_B_OFFSET   0xBB
#define PERIPHS_PIN_MUX_C_OFFSET   0xBC
#define PERIPHS_PIN_MUX_D_OFFSET   0xBD
#define PERIPHS_PIN_MUX_E_OFFSET   0xBE
#define PERIPHS_PIN_MUX_F_OFFSET   0xBF

// Drive strength, 4 possible values: { 500uA, 2500uA, 3000uA, 4000uA }
#define PAD_DS_REG0A_OFFSET        0xD0
#define PAD_DS_REG1A_OFFSET        0xD1
#define PAD_DS_REG2A_OFFSET        0xD2
#define PAD_DS_REG2B_OFFSET        0xD3
#define PAD_DS_REG3A_OFFSET        0xD4
#define PAD_DS_REG4A_OFFSET        0xD5
#define PAD_DS_REG5A_OFFSET        0xD6

// Enable biasing
#define PAD_PULL_UP_EN_REG0_OFFSET 0x48
#define PAD_PULL_UP_EN_REG1_OFFSET 0x49
#define PAD_PULL_UP_EN_REG2_OFFSET 0x4A
#define PAD_PULL_UP_EN_REG3_OFFSET 0x4B
#define PAD_PULL_UP_EN_REG4_OFFSET 0x4C
#define PAD_PULL_UP_EN_REG5_OFFSET 0x4D

// Pull up or down if biasing is enabled
#define PAD_PULL_UP_REG0_OFFSET    0x3A
#define PAD_PULL_UP_REG1_OFFSET    0x3B
#define PAD_PULL_UP_REG2_OFFSET    0x3C
#define PAD_PULL_UP_REG3_OFFSET    0x3D
#define PAD_PULL_UP_REG4_OFFSET    0x3E
#define PAD_PULL_UP_REG5_OFFSET    0x3F

// Enable this pad to be used as a GPIO if not connected to any port
#define PREG_PAD_GPIO0_EN_N_OFFSET 0x10
// Contains input-output state of the pad
#define PREG_PAD_GPIO0_O_OFFSET    0x11
#define PREG_PAD_GPIO0_I_OFFSET    0x12
// Same definitions repeat
#define PREG_PAD_GPIO1_EN_N_OFFSET 0x13
#define PREG_PAD_GPIO1_O_OFFSET    0x14
#define PREG_PAD_GPIO1_I_OFFSET    0x15
#define PREG_PAD_GPIO2_EN_N_OFFSET 0x16
#define PREG_PAD_GPIO2_O_OFFSET    0x17
#define PREG_PAD_GPIO2_I_OFFSET    0x18
#define PREG_PAD_GPIO3_EN_N_OFFSET 0x19
#define PREG_PAD_GPIO3_O_OFFSET    0x1A
#define PREG_PAD_GPIO3_I_OFFSET    0x1B
#define PREG_PAD_GPIO4_EN_N_OFFSET 0x1C
#define PREG_PAD_GPIO4_O_OFFSET    0x1D
#define PREG_PAD_GPIO4_I_OFFSET    0x1E
#define PREG_PAD_GPIO5_EN_N_OFFSET 0x20
#define PREG_PAD_GPIO5_O_OFFSET    0x21
#define PREG_PAD_GPIO5_I_OFFSET    0x22

// If a register does not have a value here, it is either reserved or read-only.
pindata_t default_periphs_pinmux[] = {
    { .offset = PERIPHS_PIN_MUX_0_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_1_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_3_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_4_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_5_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_6_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_7_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_9_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_B_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_C_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_D_OFFSET, .value = 0x0 },
    { .offset = PERIPHS_PIN_MUX_E_OFFSET, .value = 0x0 },
    { .offset = PAD_DS_REG0A_OFFSET, .value = 0xAAAAAAAA },
    { .offset = PAD_DS_REG1A_OFFSET, .value = 0xAAAA9AAA },
    { .offset = PAD_DS_REG2A_OFFSET, .value = 0x55955AAA },
    { .offset = PAD_DS_REG2B_OFFSET, .value = 0xAAAAAA55 },
    { .offset = PAD_DS_REG3A_OFFSET, .value = 0xAAAA55AA },
    { .offset = PAD_DS_REG4A_OFFSET, .value = 0xAAAAAAA5 },
    { .offset = PAD_DS_REG5A_OFFSET, .value = 0x5695555A },
    { .offset = PAD_PULL_UP_EN_REG0_OFFSET, .value = 0x0000FFFF },
    { .offset = PAD_PULL_UP_EN_REG1_OFFSET, .value = 0x000000FF },
    { .offset = PAD_PULL_UP_EN_REG2_OFFSET, .value = 0x0007FFFF },
    { .offset = PAD_PULL_UP_EN_REG3_OFFSET, .value = 0x000001FF },
    { .offset = PAD_PULL_UP_EN_REG4_OFFSET, .value = 0x00003FFF },
    { .offset = PAD_PULL_UP_EN_REG5_OFFSET, .value = 0x0000FFFF },
    { .offset = PAD_PULL_UP_REG0_OFFSET, .value = 0x0000CFFF },
    { .offset = PAD_PULL_UP_REG1_OFFSET, .value = 0x000000FF },
    { .offset = PAD_PULL_UP_REG2_OFFSET, .value = 0x0005FFBF },
    { .offset = PAD_PULL_UP_REG3_OFFSET, .value = 0x0000010F },
    { .offset = PAD_PULL_UP_REG4_OFFSET, .value = 0x0000C1FF },
    { .offset = PAD_PULL_UP_REG5_OFFSET, .value = 0x0000C000 },
    { .offset = PREG_PAD_GPIO0_EN_N_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO0_O_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO0_I_OFFSET, .value = 0x0 },
    { .offset = PREG_PAD_GPIO1_EN_N_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO1_O_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO1_I_OFFSET, .value = 0x0 },
    { .offset = PREG_PAD_GPIO2_EN_N_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO2_O_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO2_I_OFFSET, .value = 0x0 },
    { .offset = PREG_PAD_GPIO3_EN_N_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO3_O_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO3_I_OFFSET, .value = 0x0 },
    { .offset = PREG_PAD_GPIO4_EN_N_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO4_O_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO4_I_OFFSET, .value = 0x0 },
    { .offset = PREG_PAD_GPIO5_EN_N_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO5_O_OFFSET, .value = 0xFFFFFFFF },
    { .offset = PREG_PAD_GPIO5_I_OFFSET, .value = 0x0 }
};
