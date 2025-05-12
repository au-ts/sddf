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
#include <sddf/util/string.h>
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

// From Linux's Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
// Special values for pad_setting:
// Indicate this pin does not need config
#define NO_PAD_CTL (1 << 31)

typedef struct __attribute__((packed)) iomuxc_config {
    const uint32_t mux_reg;         /* Contains offset of mux registers */
    const uint32_t conf_reg;        /* Offset of pad configuration register */
    const uint32_t input_reg;       /* Offset of select input register */
    const uint32_t mux_val;         /* Mux values to be applied */
    const uint32_t input_val;       /* Select input values to be applied */
    const uint32_t pad_setting;     /* Pad configuration values to be applied */
    const uint32_t phandle;
    const char *src_device_path;    /* Device tree path of the device that this config data is a part of */
    const char *config_name;        /* Config name as referenced by the device in the `pinctrl-names` prop */
    const char *pinctrl_group_name; /* Config name as referenced by the iomuxc */
} iomuxc_config_t;

// Data from Device Tree that is linked during compile time.
extern const iomuxc_config_t iomuxc_configs[];
extern const uint32_t num_iomuxc_configs;

bool sanity_check_pinctrl_reg_offset(uint32_t offset)
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
    if (!sanity_check_pinctrl_reg_offset(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);
    *ret = *mux_reg_vaddr;
    return true;
}

bool set_mux(uint32_t offset, uint32_t val)
{
    // @billn: should really check the bound of the offset. to fix
    if (!sanity_check_pinctrl_reg_offset(offset)) {
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
        LOG_DRIVER("mux reg: 0x%x = 0x%x, input reg: 0x%x = 0x%x, pad conf reg: 0x%x = 0x%x from phandle 0x%x of device `%s` as part of its `%s` configuration in group `%s`\n",
                   iomuxc_configs[i].mux_reg,
                   iomuxc_configs[i].mux_val, iomuxc_configs[i].input_reg, iomuxc_configs[i].input_val,
                   iomuxc_configs[i].conf_reg, iomuxc_configs[i].pad_setting, iomuxc_configs[i].phandle, iomuxc_configs[i].src_device_path,
                   iomuxc_configs[i].config_name, iomuxc_configs[i].pinctrl_group_name);
    }
}

void reset_pinmux_to_default()
{
    int nums_pin_set = 0;
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        if (sddf_strcmp(iomuxc_configs[i].config_name, "default") != 0) {
            continue;
        }
        nums_pin_set += 1;

        // Write mux settings
        if (!set_mux(iomuxc_configs[i].mux_reg, iomuxc_configs[i].mux_val)) {
            while (true) {};
        }

        // Write input settings
        if (iomuxc_configs[i].input_reg) {
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
                // uint32_t val = iomuxc_configs[i].input_val;
                // uint8_t select = val & 0xff;
                // uint8_t width = (val >> 8) & 0xff;
                // uint8_t shift = (val >> 16) & 0xff;
                // uint32_t mask = ((1 << width) - 1) << shift;
                // /*
                //     * The iomuxc_configs[i].input_reg here is actually some
                //     * IOMUXC general purpose register, not
                //     * regular select input register.
                // */
                // if (!read_mux(iomuxc_configs[i].input_reg, &val)) {
                //     while (true) {};
                // }
                // val &= ~mask;
                // val |= select << shift;
                // iomuxc_configs[i].input_val = val;
                // if (!set_mux(iomuxc_configs[i].input_reg, iomuxc_configs[i].input_val)) {
                //     while (true) {};
                // }

                LOG_DRIVER("quirky\n");
                while (1);
            }

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

    LOG_DRIVER("reset_pinmux_to_default(): set %d pins\n", nums_pin_set);
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 0);
    assert(device_resources.num_regions == 1);

    iomuxc_dev_base = (uintptr_t) device_resources.regions[0].region.vaddr;

    debug_dts_print();
    reset_pinmux_to_default();

    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}
