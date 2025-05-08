/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
Pinctrl driver for the iMX8 SoC based platforms.
Tested on MaaXBoard (imx8mq), imx8mq-evk, imx8mm-evk and imx8mp-evk.

Documents referenced:
Linux: Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
U-Boot: drivers/pinctrl/nxp/pinctrl-imx.c
*/

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PINCTRL DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PINCTRL DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

uintptr_t iomuxc_dev_base;
// The registers are only within iomuxc_dev_base + IOMUXC_DEVICE_BASE_PAD and
// iomuxc_dev_base + IOMUXC_DEVICE_BASE_PAD + IOMUXC_DEVICE_EFFECTIVE_SIZE

// @billn to fix once multi DT-nodes device works in sdfgen
// General Purpose Registers: a memory region contiguous with the iomuxc device.
// Contains control registers to pads that can't be mux'ed. E.g. HDMI, DDR, DSI, PCIe,...
// uintptr_t iomuxc_gpr_base;

// From Linux's Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
// Special values for pad_setting:
// Indicate this pin does not need config
#define NO_PAD_CTL (1 << 31)
// Software Input On Field.
// Force the selected mux mode input path no matter of MUX_MODE functionality.
// By default the input path is determined by functionality of the selected
// mux mode (regular). This bit will be set in "pad_setting"
#define PAD_SION (1 << 30)

// If the above bit is set, clear it from "pad_setting" then set this bit in "mux_reg"
#define MUX_SION (1 << 4)

typedef struct iomuxc_config {
    uint32_t mux_reg;     /* Contains offset of mux registers */
    uint32_t conf_reg;    /* Offset of pad configuration register */
    uint32_t input_reg;   /* Offset of select input register */
    uint32_t mux_val;     /* Mux values to be applied */
    uint32_t input_val;   /* Select input values to be applied */
    uint32_t pad_setting; /* Pad configuration values to be applied */
} iomuxc_config_t;

// Data from Device Tree that is linked during compile time.
extern iomuxc_config_t iomuxc_configs[];
extern const uint32_t num_iomuxc_configs;

bool check_offset_4_bytes_aligned(uint32_t offset)
{
    if (offset % 4 == 0) {
        return true;
    } else {
        LOG_DRIVER_ERR("offset is not 4 bytes aligned\n");
        return false;
    }
}

bool read_mux(uint32_t offset, uint32_t *ret)
{
    // @billn: should really check the bound of the offset. to fix
    if (!check_offset_4_bytes_aligned(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);
    *ret = *mux_reg_vaddr;
    return true;
}

bool set_mux(uint32_t offset, uint32_t val)
{
    // @billn: should really check the bound of the offset. to fix
    if (!check_offset_4_bytes_aligned(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);
    *mux_reg_vaddr = val;

    // Make sure the register is programmed with the expected value
    if (*mux_reg_vaddr != val) {
        LOG_DRIVER_ERR("write was not completed, real != expected: %x != %x", *mux_reg_vaddr, val);
        return false;
    }
    return true;
}

void debug_dts_print()
{
    LOG_DRIVER("nums of config is %u\n", num_iomuxc_configs);
    LOG_DRIVER("data dump begin...one pin per line\n");
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        LOG_DRIVER("mux reg: 0x%x = 0x%x, input reg: 0x%x = 0x%x, pad conf reg: 0x%x = 0x%x. ", iomuxc_configs[i].mux_reg,
                   iomuxc_configs[i].mux_val, iomuxc_configs[i].input_reg, iomuxc_configs[i].input_val,
                   iomuxc_configs[i].conf_reg, iomuxc_configs[i].pad_setting);

        if (iomuxc_configs[i].pad_setting & PAD_SION) {
            LOG_DRIVER("Software Input On Field.\n");
        } else if (iomuxc_configs[i].pad_setting & NO_PAD_CTL) {
            LOG_DRIVER("Do not config.\n");
        } else {
            LOG_DRIVER("Normal.\n");
        }

        if (iomuxc_configs[i].input_val >> 24 == 0xFF) {
            LOG_DRIVER("Quirky select input.\n");
        }
    }
}

void process_dts_values_to_register_values()
{
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        // For pins that have SION bit set in "pad_setting", flip it in "mux_val" and clear it from "pad_setting"
        if (iomuxc_configs[i].pad_setting & PAD_SION) {
            iomuxc_configs[i].mux_reg |= MUX_SION;
            iomuxc_configs[i].pad_setting &= ~PAD_SION;
        }

        // Handle input settings. From U-Boot:
        /*
            * If the select input value begins with 0xff,
            * it's a quirky select input and the value should
            * be interpreted as below.
            *     31     23      15      7        0
            *     | 0xff | shift | width | select |
            * It's used to work around the problem that the
            * select input for some pin is not implemented in
            * the select input register but in some general
            * purpose register. We encode the select input
            * value, width and shift of the bit field into
            * input_val cell of pin function ID in device tree,
            * and then decode them here for setting up the select
            * input bits in general purpose register.
        */
        if (iomuxc_configs[i].input_val >> 24 == 0xff) {
            uint32_t val = iomuxc_configs[i].input_val;
            uint8_t select = val & 0xff;
            uint8_t width = (val >> 8) & 0xff;
            uint8_t shift = (val >> 16) & 0xff;
            uint32_t mask = ((1 << width) - 1) << shift;
            /*
                * The iomuxc_configs[i].input_reg here is actually some
                * IOMUXC general purpose register, not
                * regular select input register.
            */
            if (!read_mux(iomuxc_configs[i].input_reg, &val)) {
                while (true) {};
            }
            val &= ~mask;
            val |= select << shift;
            iomuxc_configs[i].input_val = val;
            if (!set_mux(iomuxc_configs[i].input_reg, iomuxc_configs[i].input_val)) {
                while (true) {};
            }
        }
    }
}

void reset_pinmux()
{
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        // Write mux settings
        if (!set_mux(iomuxc_configs[i].mux_reg, iomuxc_configs[i].mux_val)) {
            while (true) {};
        }

        // Write input settings
        if (iomuxc_configs[i].input_reg) {
            if (!set_mux(iomuxc_configs[i].input_reg, iomuxc_configs[i].input_val)) {
                while (true) {};
            }
        }

        // Write pad settings
        if (!(iomuxc_configs[i].pad_setting & NO_PAD_CTL)) {
            if (!set_mux(iomuxc_configs[i].conf_reg, iomuxc_configs[i].pad_setting)) {
                while (true) {};
            }
        }
    }
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 0);
    assert(device_resources.num_regions == 1);

    iomuxc_dev_base = (uintptr_t) device_resources.regions[0].region.vaddr;

    debug_dts_print();
    process_dts_values_to_register_values();
    reset_pinmux();

    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}
