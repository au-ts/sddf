// Copyright 2024, UNSW
// SPDX-License-Identifier: BSD-2-Clause

// Document referenced: Chapter 7.9 of Amlogic S905X3 Datasheet revision 02.

// Device registers range
#define AO_BASE_PAD (0x05 * 4) // Distance between pinctrl_ao_base and the first AO register
#define AO_LAST_REGISTER_OFFSET (0x0D * 4)
#define AO_EFFECTIVE_SIZE ((AO_LAST_REGISTER_OFFSET + BYTES_IN_32_BITS) - AO_BASE_PAD)

#define PERIPHS_BASE_PAD (0x10 * 4) // Distance between pinctrl_periphs_base and the first peripherals register
#define PERIPHS_LAST_REGISTER_OFFSET (0xD6 * 4)
#define PERIPHS_EFFECTIVE_SIZE ((PERIPHS_LAST_REGISTER_OFFSET + BYTES_IN_32_BITS) - PERIPHS_BASE_PAD)
