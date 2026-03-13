/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
Pinctrl driver for the iMX8 SoC based platforms.

Documents referenced:
[1] Linux:  Documentation/devicetree/bindings/pinctrl/fsl,imx-pinctrl.txt
[2] Linux:  drivers/pinctrl/freescale/pinctrl-imx.c
[3] U-Boot: drivers/pinctrl/nxp/pinctrl-imx.c
*/

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
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
#define LOG_DRIVER_ERR_FATAL(...) do{ sddf_printf("PINCTRL DRIVER|FATAL ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

uintptr_t iomuxc_dev_base;

// [1]
// Special values for pad_setting:
// Indicate this pin does not need config
#define NO_PAD_CTL (1 << 31)

typedef struct __attribute__((packed)) pinctrl_pin_register {
    const uint32_t mux_reg;         /* Contains offset of mux registers */
    const uint32_t conf_reg;        /* Offset of pad configuration register */
    const uint32_t input_reg;       /* Offset of select input register */
    const uint32_t mux_val;         /* Mux values to be applied */
    const uint32_t input_val;       /* Select input values to be applied */
    const uint32_t pad_setting;     /* Pad configuration values to be applied */
} pinctrl_pin_register_t;

typedef struct __attribute__((packed)) pinctrl_client_device_state {
    const char *state_name;
    const uint32_t num_pins;
    const pinctrl_pin_register_t *pins_reg;
} pinctrl_client_device_state_t;

typedef struct __attribute__((packed)) pinctrl_client_device_data {
    const char *dev_dt_path;   /* Device tree path of this particular device that needs pinctrl configuration */
    const char *dev_dt_alias;
    const uint32_t num_states; /* Number of pinctrl states required as defined in the `pinctrl-names` prop */
    const pinctrl_client_device_state_t **states;
} pinctrl_client_device_data_t;

// Data from Device Tree that is linked during compile time.
#define CONFIG_MAGIC 0x696D70696E6D7578 // "impinmux"
extern const uint64_t pinctrl_config_data_magic;
extern const pinctrl_client_device_data_t pinctrl_client_devices_configs[];
extern const uint32_t num_pinctrl_client_devices_configs;

static bool sanity_check_pinctrl_reg_offset(uint32_t offset)
{
    if (offset % 4 == 0) {
        return true;
    } else {
        LOG_DRIVER_ERR_FATAL("offset 0x%x is not 4 bytes aligned\n", offset);
        return false;
    }
}

static bool read_mux(uint32_t offset, uint32_t *ret)
{
    if (!sanity_check_pinctrl_reg_offset(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);
    *ret = *mux_reg_vaddr;
    return true;
}

static bool set_mux(uint32_t offset, uint32_t val)
{
    if (!sanity_check_pinctrl_reg_offset(offset)) {
        return false;
    }

    volatile uint32_t *mux_reg_vaddr = (uint32_t *)(iomuxc_dev_base + (uintptr_t)offset);
    *mux_reg_vaddr = val;

    if (*mux_reg_vaddr != val) {
        LOG_DRIVER_ERR_FATAL("write was not completed, real != expected: %x != %x", *mux_reg_vaddr, val);
        return false;
    }
    return true;
}

static void debug_print_pinctrl_config_data(void)
{
    LOG_DRIVER("STARTING PINCTRL CONFIG DUMP\n");
    LOG_DRIVER("Total %u devices need pinctrl configuration.\n", num_pinctrl_client_devices_configs);
    for (int i = 0; i < num_pinctrl_client_devices_configs; i++) {
        LOG_DRIVER("** %s with alias %s have the following %d states:\n", pinctrl_client_devices_configs[i].dev_dt_path,
                   pinctrl_client_devices_configs[i].dev_dt_alias, pinctrl_client_devices_configs[i].num_states);
        for (int j = 0; j < pinctrl_client_devices_configs[i].num_states; j++) {
            LOG_DRIVER("* State '%s' at index %d have %u pins:\n",
                       pinctrl_client_devices_configs[i].states[j]->state_name, j,
                       pinctrl_client_devices_configs[i].states[j]->num_pins);
            for (int k = 0; k < pinctrl_client_devices_configs[i].states[j]->num_pins; k++) {
                LOG_DRIVER("mux reg: 0x%x = 0x%x, input reg: 0x%x = 0x%x, pad conf reg: 0x%x = 0x%x\n",
                           pinctrl_client_devices_configs[i].states[j]->pins_reg[k].mux_reg,
                           pinctrl_client_devices_configs[i].states[j]->pins_reg[k].mux_val,
                           pinctrl_client_devices_configs[i].states[j]->pins_reg[k].input_reg,
                           pinctrl_client_devices_configs[i].states[j]->pins_reg[k].input_val,
                           pinctrl_client_devices_configs[i].states[j]->pins_reg[k].conf_reg,
                           pinctrl_client_devices_configs[i].states[j]->pins_reg[k].pad_setting);
            }
        }
    }
    LOG_DRIVER("---------------------------------------------------------------\n");
}

static void pinctrl_set_state(pinctrl_client_device_state_t state)
{
    for (int j = 0; j < state.num_pins; j++) {
        assert(set_mux(state.pins_reg[j].mux_reg, state.pins_reg[j].mux_val));
        if (state.pins_reg[j].input_reg) {
            // We don't support "quirky" select input values of [2] (checkout tag v6.1, line 196).
            // As it was only ever used in vendor kernels of old imx6 and imx7 boards and never made
            // it to upstream Linux.
            assert(state.pins_reg[j].input_val >> 24 != 0xff);

            assert(set_mux(state.pins_reg[j].input_reg, state.pins_reg[j].input_val));
        }
        if (!(state.pins_reg[j].pad_setting & NO_PAD_CTL)) {
            assert(set_mux(state.pins_reg[j].conf_reg, state.pins_reg[j].pad_setting));
        }
    }
}

static void pinctrl_reset_all_default(void)
{
    for (int i = 0; i < num_pinctrl_client_devices_configs; i++) {
        pinctrl_client_device_data_t client_device = pinctrl_client_devices_configs[i];
        assert(client_device.num_states > 0);
        pinctrl_client_device_state_t default_state = *(pinctrl_client_devices_configs[i].states[0]);
        assert(strcmp(default_state.state_name, "default") == 0);

        LOG_DRIVER("Setting dev %s to default pinctrl config with total %u pins.\n", client_device.dev_dt_path,
                   default_state.num_pins);
        pinctrl_set_state(default_state);
    }
}

void init(void)
{
    assert(device_resources_check_magic(&device_resources));
    assert(device_resources.num_irqs == 0);
    assert(device_resources.num_regions == 1);

    assert(pinctrl_config_data_magic == CONFIG_MAGIC);
    assert(num_pinctrl_client_devices_configs >= 1);

    iomuxc_dev_base = (uintptr_t)device_resources.regions[0].region.vaddr;

    debug_print_pinctrl_config_data();
    pinctrl_reset_all_default();

    LOG_DRIVER("INIT OK\n");
}

void notified(microkit_channel ch)
{
    LOG_DRIVER_ERR("received ntfn on unexpected channel %u\n", ch);
}
