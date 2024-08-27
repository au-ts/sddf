/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>
#include <sddf/pinctrl/protocol.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PINCTRL DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PINCTRL DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// From Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
// Special values for pad_setting:
// Indicate this pin does not need config
#define NO_PAD_CTL (1 << 31)
// Software Input On Field.
// Force the selected mux mode input path no matter of MUX_MODE functionality.
// By default the input path is determined by functionality of the selected
// mux mode (regular).
#define SION (1 << 30)

uintptr_t iomuxc_base;

typedef struct iomuxc_config {
    uint32_t mux_reg;     /* Contains offset of mux registers */
    uint32_t conf_reg;    /* Offset of pad configuration register */
    uint32_t input_reg;   /* Offset of select input register */
    uint32_t mux_val;     /* Mux values to be applied */
    uint32_t input_val;   /* Select input values to be applied */
    uint32_t pad_setting; /* Pad configuration values to be applied */
} iomuxc_config_t;

extern const iomuxc_config_t iomuxc_configs[];
extern const uint32_t num_iomuxc_configs;

void init(void) {
    LOG_DRIVER("started\n");
    LOG_DRIVER("nums of config is %u\n", num_iomuxc_configs);

    LOG_DRIVER("data dump begin...one pin per line\n");
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        LOG_DRIVER("mux reg: 0x%x = %u, input reg: 0x%x = %u, pad conf reg: 0x%x = %u. ", 
                    iomuxc_configs[i].mux_reg, iomuxc_configs[i].mux_val, 
                    iomuxc_configs[i].input_reg, iomuxc_configs[i].input_val, 
                    iomuxc_configs[i].conf_reg, iomuxc_configs[i].pad_setting
        );
        if (iomuxc_configs[i].pad_setting & SION) {
            LOG_DRIVER("Software Input On Field.\n");
        } else {
            LOG_DRIVER("Normal.\n");
        }
    }

    LOG_DRIVER("initialising...\n");
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        LOG_DRIVER("writing pin #%u\n", i);
        uint32_t *mux_reg_offset = (uint32_t *) (iomuxc_base + (uintptr_t) iomuxc_configs[i].mux_reg);
        *mux_reg_offset = iomuxc_configs[i].mux_val;

        uint32_t *conf_reg_offset = (uint32_t *) (iomuxc_base + (uintptr_t) iomuxc_configs[i].conf_reg);
        *conf_reg_offset = iomuxc_configs[i].pad_setting;

        uint32_t *input_reg_offset = (uint32_t *) (iomuxc_base + (uintptr_t) iomuxc_configs[i].input_reg);
        *input_reg_offset = iomuxc_configs[i].input_val;
    }

    LOG_DRIVER("pinctrl device initialisation done\n");
}

void notified(microkit_channel ch) {
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo) {
    switch (microkit_msginfo_get_label(msginfo)) {

    case SDDF_PINCTRL_SET_MUX: {
        if (microkit_msginfo_get_count(msginfo) != SET_MUX_REQ_NUM_ARGS) {
            LOG_DRIVER_ERR("Set mux PPC from channel %u does not have the correct number of arguments %lu != %d\n", ch, microkit_msginfo_get_count(msginfo), SET_MUX_REQ_NUM_ARGS);
            return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
        }

        uint32_t reg_offset = (uint32_t) microkit_mr_get(SET_MUX_REQ_OFFSET);
        uint32_t reg_val = (uint32_t) microkit_mr_get(SET_MUX_REQ_VALUE);

        uint32_t *mux_reg_offset = (uint32_t *) (iomuxc_base + (uintptr_t) reg_offset);
        *mux_reg_offset = reg_val;
        break;
    }

    case SDDF_PINCTRL_QUERY_DTS: {
        if (microkit_msginfo_get_count(msginfo) != QUERY_DTS_REQ_NUM_ARGS) {
            LOG_DRIVER_ERR("Query DTS PPC from channel %u does not have the correct number of arguments %lu != %d\n", ch, microkit_msginfo_get_count(msginfo), QUERY_DTS_REQ_NUM_ARGS);
            return microkit_msginfo_new(SDDF_PINCTRL_INVALID_ARGS, 0);
        }

        uint32_t reg_offset = (uint32_t) microkit_mr_get(QUERY_DTS_REQ_OFFSET);

        bool found = false;
        uint32_t found_value;
        for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
            if (reg_offset == iomuxc_configs[i].mux_reg) {
                found_value = iomuxc_configs[i].mux_val;
                found = true;
                break;
            }
            
            if (reg_offset == iomuxc_configs[i].conf_reg) {
                found_value = iomuxc_configs[i].pad_setting;
                found = true;
                break;
            }

            if (reg_offset == iomuxc_configs[i].input_reg) {
                found_value = iomuxc_configs[i].input_val;
                found = true;
                break;
            }
        }

        if (found) {
            microkit_mr_set(QUERY_DTS_RESP_VALUE, found_value);
            return microkit_msginfo_new(SDDF_PINCTRL_SUCCESS, QUERY_DTS_RESP_NUM_RESULTS);
        } else {
            return microkit_msginfo_new(SDDF_PINCTRL_NOT_IN_DTS, 0);
        }
    }

    default:
        LOG_DRIVER_ERR("Unknown request %lu to pinctrl from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        return microkit_msginfo_new(SDDF_PINCTRL_UNKNOWN_REQ, 0);
    }

    return microkit_msginfo_new(SDDF_PINCTRL_SUCCESS, 0);
}
