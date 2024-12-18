/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Pinctrl driver. Tested on MaaXBoard (imx8mq), imx8mq-evk and imx8mm-evk.

// Documents referenced:
// Linux: Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
// U-Boot: drivers/pinctrl/nxp/pinctrl-imx.c

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/pinctrl/protocol.h>

#include <pinctrl_chips.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PINCTRL DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PINCTRL DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define BYTES_IN_32_BITS 4

// Contains 32-bits wide registers to mux individual pads on the SoC.
#define IOMUXC_DEVICE_SIZE 0x10000
#define IOMUXC_DEVICE_BASE_PAD 0x14 // Distance between iomuxc_dev_base and first mux register

// Size of all registers inclusive
#ifdef SOC_IMX8MQ_EVK
#define IOMUXC_DEVICE_EFFECTIVE_SIZE 0x520
#endif
#ifdef SOC_IMX8MM_EVK
#define IOMUXC_DEVICE_EFFECTIVE_SIZE 0x538
#endif

uintptr_t iomuxc_dev_base;
// The registers are only within iomuxc_dev_base + IOMUXC_DEVICE_BASE_PAD and
// iomuxc_dev_base + IOMUXC_DEVICE_BASE_PAD + IOMUXC_DEVICE_EFFECTIVE_SIZE

// General Purpose Registers: a memory region contiguous with the iomuxc device.
// Contains control registers to pads that can't be mux'ed. E.g. HDMI, DDR, DSI, PCIe,...
#define IOMUXC_GPR_SIZE 0x10000
#define IOMUXC_GPR_EFFECTIVE_SIZE 0xC0 // Size of all registers inclusive
uintptr_t iomuxc_gpr_base;
// The registers are only within iomuxc_gpr_base and iomuxc_gpr_base + IOMUXC_GPR_EFFECTIVE_SIZE

// Phys and virt memory layout:
// iomuxc_dev_base | ... | iomuxc_dev_base + 0xffff | iomuxc_gpr_base

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

bool check_offset_bound(uint32_t offset)
{
    if (offset >= IOMUXC_DEVICE_BASE_PAD
        && offset <= IOMUXC_DEVICE_BASE_PAD + IOMUXC_DEVICE_EFFECTIVE_SIZE - BYTES_IN_32_BITS) {
        // Offset valid in iomuxc_dev_base
        return true;
    } else {
        if (offset >= IOMUXC_DEVICE_SIZE
            && offset <= IOMUXC_DEVICE_SIZE + IOMUXC_GPR_EFFECTIVE_SIZE - BYTES_IN_32_BITS) {
            // Offset valid in iomuxc_gpr_base
            return true;
        }
    }

    LOG_DRIVER_ERR("offset is out of bound\n");
    return false;
}

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
    if (!check_offset_bound(offset) || !check_offset_4_bytes_aligned(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);

    asm volatile("" : : : "memory");
    *ret = *mux_reg_vaddr;
    asm volatile("" : : : "memory");

    return true;
}

bool set_mux(uint32_t offset, uint32_t val)
{
    if (!check_offset_bound(offset) || !check_offset_4_bytes_aligned(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);

    asm volatile("" : : : "memory");
    *mux_reg_vaddr = val;
    asm volatile("" : : : "memory");

    // Make sure the write actually happened
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
        LOG_DRIVER("mux reg: 0x%x = %u, input reg: 0x%x = %u, pad conf reg: 0x%x = %u. ", iomuxc_configs[i].mux_reg,
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

        // All these value changes are saved into the info array so that
        // a query DTS call returns the exact value what was written into memory.
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
    LOG_DRIVER("starting\n");
    if (iomuxc_gpr_base != iomuxc_dev_base + IOMUXC_DEVICE_SIZE) {
        LOG_DRIVER_ERR(
            "the GPR region must be mapped contiguously after the normal mux registers region in virtual memory\n");
        while (true) {};
    }

    debug_dts_print();
    process_dts_values_to_register_values();
    reset_pinmux();

    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    switch (microkit_msginfo_get_label(msginfo)) {

    case SDDF_PINCTRL_READ_MUX: {
        if (microkit_msginfo_get_count(msginfo) != READ_MUX_REQ_NUM_ARGS) {
            LOG_DRIVER_ERR("Read mux PPC from channel %u does not have the correct number of arguments %lu != %d\n", ch,
                           microkit_msginfo_get_count(msginfo), READ_MUX_REQ_NUM_ARGS);
            return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
        }

        sddf_pinctrl_chip_idx_t chip = (sddf_pinctrl_chip_idx_t)microkit_mr_get(READ_MUX_REQ_CHIP_IDX);
        if (chip >= PINCTRL_NUM_CHIPS) {
            LOG_DRIVER_ERR("Read mux PPC from channel %u gave an unknown chip index %d\n", ch, chip);
        }

        uint32_t reg_offset = (uint32_t)microkit_mr_get(READ_MUX_REQ_OFFSET);
        uint32_t reg_val;

        if (read_mux(reg_offset, &reg_val)) {
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
