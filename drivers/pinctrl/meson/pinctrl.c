/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Pinctrl driver. Tested on OdroidC4 (Amlogic S903X3)

// Documents referenced:
// Amlogic S905X3 Datasheet revision 2
// Linux: drivers/pinctrl/meson/pinctrl-meson-g12a.c
// Linux: drivers/pinctrl/meson/pinctrl-meson.c

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/pinctrl/protocol.h>

#include <pinctrl_chips.h>
#include <pinctrl_memranges.h>

#include "odroidc4.h"

// Logging
#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PINCTRL DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PINCTRL DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// Memory definitions
#define MUX_REG_ADDR(base, offset) ((uint32_t *) (base + offset))
#define PINMUX_DATA_MAGIC 0x73ABC62F

// Device mapped
uintptr_t pinctrl_ao_base;
uintptr_t pinctrl_periphs_base;

// Data from DTS prepared by Python script
extern pindata_t ao_registers[];
extern const uint32_t num_ao_registers;

extern pindata_t peripheral_registers[];
extern const uint32_t num_peripheral_registers;

extern const uint32_t pinmux_data_magic;

// Helper functions
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

    // Make sure the write actually happened
    if (*vaddr != val) {
        LOG_DRIVER_ERR("write was not completed, real != expected: %x != %x", *vaddr, val);
        return false;
    }

    return true;
}

void initialise_ao_chip(void) {
    sddf_printf_("Initialising Always-On GPIO chip to values in DTS\n");
    for (uint32_t i = 0; i < num_ao_registers; i += 1) {
        uint32_t curr;
        read_mux(MUX_REG_ADDR(pinctrl_ao_base, ao_registers[i].offset), &curr);
        sddf_printf_("offset %x, curr = %x, dest = %x\n", ao_registers[i].offset, curr, ao_registers[i].value);
    
        set_mux(MUX_REG_ADDR(pinctrl_ao_base, ao_registers[i].offset), ao_registers[i].value);
    }
}

void fix_peripherals_chip_offset(void) {
    // The peripherals pinmux device physical address isn't aligned on page boundary whereas
    // memory regions can only be mapped on page boundary, we need to offset the page boundary address
    // into the actual pinmux device.
    pinctrl_periphs_base += 0x400;
}

void default_initialise_peripherals_chip(void) {
    sddf_printf_("Default initialising peripherals GPIO chip to values in datasheet\n");
    for (int i = 0; i < sizeof(default_periphs_pinmux) / sizeof(default_periphs_pinmux[0]); i += 1) {
        sddf_printf_("offset %x = %x\n", default_periphs_pinmux[i].offset, default_periphs_pinmux[i].value);
        set_mux(MUX_REG_ADDR(pinctrl_periphs_base, default_periphs_pinmux[i].offset), default_periphs_pinmux[i].value);
    }
}

void initialise_peripherals_chip(void) {
    sddf_printf_("Initialising peripherals GPIO chip to values in DTS\n");
    for (uint32_t i = 0; i < num_peripheral_registers; i += 1) {
        uint32_t curr;
        read_mux(MUX_REG_ADDR(pinctrl_periphs_base, peripheral_registers[i].offset), &curr);
        sddf_printf_("offset %x, curr = %x, dest = %x\n", peripheral_registers[i].offset, curr, peripheral_registers[i].value);
    
        set_mux(MUX_REG_ADDR(pinctrl_periphs_base, peripheral_registers[i].offset), peripheral_registers[i].value);
    }
}

void init(void) {
    LOG_DRIVER("starting\n");

    if (pinmux_data_magic != PINMUX_DATA_MAGIC) {
        LOG_DRIVER_ERR("magic does not match");
    }

    initialise_ao_chip();

    fix_peripherals_chip_offset();
    default_initialise_peripherals_chip();
    initialise_peripherals_chip();

    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch) {
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo) {
    switch (microkit_msginfo_get_label(msginfo)) {

    case SDDF_PINCTRL_READ_MUX: {
        if (microkit_msginfo_get_count(msginfo) != READ_MUX_REQ_NUM_ARGS) {
            LOG_DRIVER_ERR(
                "Read mux PPC from channel %u does not have the correct number of arguments %lu != %d\n", 
                ch, 
                microkit_msginfo_get_count(msginfo), READ_MUX_REQ_NUM_ARGS
            );
            return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
        }

        uint32_t reg_offset = (uint32_t) microkit_mr_get(READ_MUX_REQ_OFFSET);
        uint32_t *reg_vaddr;
        uint32_t reg_val;

        sddf_pinctrl_chip_idx_t chip = (sddf_pinctrl_chip_idx_t) microkit_mr_get(READ_MUX_REQ_CHIP_IDX);
        if (chip == PINCTRL_CHIP_AO) {
            if (reg_offset >= AO_BASE_PAD && reg_offset <= AO_LAST_REGISTER_OFFSET) {
                reg_vaddr = (uint32_t *) (pinctrl_ao_base + reg_offset);
            } else {
                return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
            }
        } else if (chip == PINCTRL_CHIP_PERIPHERALS) {
            if (reg_offset >= PERIPHS_BASE_PAD && reg_offset <= PERIPHS_LAST_REGISTER_OFFSET) {
                reg_vaddr = (uint32_t *) (pinctrl_periphs_base + reg_offset);
            } else {
                return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
            }
        } else {
            LOG_DRIVER_ERR("Read mux PPC from channel %u gave an unknown chip index %d\n", ch, chip);
            return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
        }

        if (read_mux(reg_vaddr, &reg_val)) {
            microkit_mr_set(READ_MUX_RESP_VALUE, reg_val);
            return microkit_msginfo_new(SDDF_PINCTRL_SUCCESS, READ_MUX_RESP_NUM_RESULTS);
        } else {
            return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
        }
    }

    default:
        LOG_DRIVER_ERR("Unknown request %lu to pinctrl from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        return microkit_msginfo_new(SDDF_PINCTRL_UNKNOWN_REQ, 0);
    }
}
