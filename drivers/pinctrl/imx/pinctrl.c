#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/pinctrl/protocol.h>

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("PINCTRL DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("PINCTRL DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

uintptr_t iomuxc_base;

typedef struct iomuxc_config {
    uint32_t mux_reg;     /* Contains offset of mux registers */
    uint32_t conf_reg;    /* Offset of pad configuration register */
    uint32_t input_reg;   /* Offset of select input register */
    uint32_t mux_val;     /* Mux values to be applied */
    uint32_t input_val;   /* Select input values to be applied */
    uint32_t pad_setting; /* Pad configuration values to be applied */
} iomuxc_config_t;

extern iomuxc_config_t iomuxc_configs[];
extern uint32_t num_iomuxc_configs;

void init(void) {
    LOG_DRIVER("started\n");
    LOG_DRIVER("nums of config is %u\n", num_iomuxc_configs);

    LOG_DRIVER("data dump begin...one pin per line\n");
    for (uint32_t i = 0; i < num_iomuxc_configs; i += 1) {
        LOG_DRIVER("%u %u %u %u %u %u\n", iomuxc_configs[i].mux_reg, iomuxc_configs[i].conf_reg, iomuxc_configs[i].input_reg, iomuxc_configs[i].mux_val, iomuxc_configs[i].input_val, iomuxc_configs[i].pad_setting);
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
        uint32_t reg_offset = (uint32_t) microkit_mr_get(0);
        uint32_t reg_val = (uint32_t) microkit_mr_get(1);

        uint32_t *mux_reg_offset = (uint32_t *) (iomuxc_base + (uintptr_t) reg_offset);
        *mux_reg_offset = reg_val;
        break;
    }
    default:
        LOG_DRIVER_ERR("Unknown request %lu to pinctrl from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    microkit_mr_set(0, 1);
    return microkit_msginfo_new(0, 1);
}
