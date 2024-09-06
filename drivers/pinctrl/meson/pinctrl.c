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

bool check_vaddr_4_bytes_aligned(uint32_t *vaddr) {
    if (((uintptr_t) vaddr) % 4 == 0) {
        return true;
    } else {
        LOG_DRIVER_ERR("vaddr is not 4 bytes aligned\n");
        return false;
    }
}

bool read_mux(uint32_t *vaddr, uint32_t *ret) {
    if (!check_vaddr_4_bytes_aligned(vaddr)) {
        return false;
    }

    asm volatile("" : : : "memory");
    *ret = *vaddr;
    asm volatile("" : : : "memory");

    return true;
}

bool set_mux(uint32_t *vaddr, uint32_t val) {
    if (!check_vaddr_4_bytes_aligned(vaddr)) {
        return false;
    }

    asm volatile("" : : : "memory");
    *vaddr = val;
    asm volatile("" : : : "memory");

    return true;
}

void reset_periphs_pinmux_to_default(void) {
    LOG_DRIVER("in reset_periphs_pinmux_to_default\n");
    for (int i = 0; i < sizeof(default_periphs_pinmux) / sizeof(pindata_t); i++) {
        if (!set_mux(MUX_REG_ADDR(pinctrl_periphs_base, default_periphs_pinmux[i].offset), default_periphs_pinmux[i].value)) {
            LOG_DRIVER_ERR("cannot reset peripherals pinmux to default values");
            while (true) {};
        } else {
            LOG_DRIVER("written default value %x to offset %x of peripherals pinmux\n", default_periphs_pinmux[i].value, default_periphs_pinmux[i].offset);
        }
    }
}

void init(void) {
    LOG_DRIVER("starting\n");

    // The peripherals pinmux device physical address isn't aligned on page boundary whereas
    // memory regions can only be mapped on page bondary, we need to offset the page boundary address
    // into the pinmux device.
    pinctrl_periphs_base += 0x400;

    reset_periphs_pinmux_to_default();

    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch) {
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}

