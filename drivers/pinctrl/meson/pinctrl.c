/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Pinctrl driver. Tested on OdroidC4 (Amlogic S903X3)

// Documents referenced:
// Linux: drivers/pinctrl/meson/pinctrl-meson-g12a.c
// Linux: drivers/pinctrl/meson/pinctrl-meson.c

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/pinctrl/protocol.h>

#include "odroidc4.h"

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PINCTRL DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PINCTRL DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

uintptr_t pinctrl_ao_base;
uintptr_t pinctrl_periphs_base;

extern pindata_t pinctrl_ao_configs[];
extern const uint32_t num_pinctrl_ao_configs;

extern pindata_t pinctrl_periphs_configs[];
extern const uint32_t num_pinctrl_periphs_configs;

bool check_vaddr_4_bytes_aligned(uint32_t vaddr) {
    if (vaddr % 4 == 0) {
        return true;
    } else {
        LOG_DRIVER_ERR("vaddr is not 4 bytes aligned\n");
        return false;
    }
}

bool read_mux(uintptr_t base, uint32_t offset, uint32_t *ret) {
    if (!check_vaddr_4_bytes_aligned(offset)) {
        return false;
    }
    
    volatile uint32_t *mux_reg_vaddr = (uint32_t *) base + offset;

    asm volatile("" : : : "memory");
    *ret = *mux_reg_vaddr;
    asm volatile("" : : : "memory");

    return true;
}

bool set_mux(uintptr_t base, uint32_t offset, uint32_t val) {
    if (!check_offset_4_bytes_aligned(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *) base + offset;

    asm volatile("" : : : "memory");
    *mux_reg_vaddr = val;
    asm volatile("" : : : "memory");

    return true;
}

void reset_ao_pinmux_to_default(void) {
    for (int i = 0; i < sizeof(default_ao_pinmux) / sizeof(pindata_t); i++) {
        if (!set_mux(pinctrl_ao_base, REG_ADDR(pinctrl_ao_base, default_ao_pinmux[i].offset), default_ao_pinmux[i].value)) {
            LOG_DRIVER_ERR("cannot reset AO pinmux to default values");
            while (true) {};
        } else {
            LOG_DRIVER("written default value %x to offset %x of AO pinmux\n", default_ao_pinmux[i].value, default_ao_pinmux[i].offset);
        }
    }
}

void reset_periphs_pinmux_to_default(void) {
    for (int i = 0; i < sizeof(default_periphs_pinmux) / sizeof(pindata_t); i++) {
        if (!set_mux(pinctrl_periphs_base, REG_ADDR(pinctrl_periphs_base, default_periphs_pinmux[i].offset), default_periphs_pinmux[i].value)) {
            LOG_DRIVER_ERR("cannot reset peripherals pinmux to default values");
            while (true) {};
        } else {
            LOG_DRIVER("written default value %x to offset %x of peripherals pinmux\n", default_periphs_pinmux[i].value, default_periphs_pinmux[i].offset);
        }
    }
}



void init(void) {
    LOG_DRIVER("starting\n");

    reset_ao_pinmux_to_default();
    reset_periphs_pinmux_to_default();



    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch) {
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}

