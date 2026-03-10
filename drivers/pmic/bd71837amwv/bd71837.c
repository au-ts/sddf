/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <os/sddf.h>
#include <sddf/pmic/protocol.h>
#include <sddf/pmic/driver.h>
#include <sddf/pmic/bd71837amwv-bindings.h>
#include <sddf/i2c/libi2c.h>
#include <sddf/i2c/client.h>
#include "bd71837.h"

__attribute__((__section__(".i2c_client_config"))) i2c_client_config_t i2c_config;

libi2c_conf_t libi2c_conf;
i2c_queue_handle_t queue;
uint8_t *i2c_data_region;

// TODO: add support for sdfgen to pass in PMIC i2c address
#define PMIC_I2C_ADDR (0x4b)

#ifndef I2C_DATA_REGION
#define I2C_DATA_REGION ((uint8_t *)i2c_config.data.vaddr)
#endif

// HACK: this driver skips around a limitation in microkit ... we return a success for ops
// before sending an i2c transaction as we cannot wait for a notification in the middle of
// protected(). This means that if the i2c transaction fails, the client will not know!
// There is no way to fix this other than hacking the microkit event loop locally, which isn't
// suitable for a driver. We will handle this in the future by changing microkit.

pmic_driver_state_t state;

static inline sddf_pmic_err_t pmic_not_implemented() {
    LOG_PMIC_DRIVER_ERR("This PPC not implemented for this platform!\n");
    return SDDF_PMIC_ERR_NOT_IMPLEMENTED;
}

sddf_pmic_err_t pmic_drv_enable_reg(uint64_t reg_id) {
    return pmic_not_implemented();
}

sddf_pmic_err_t pmic_drv_disable_reg(uint64_t reg_id) {
    return pmic_not_implemented();
}

sddf_pmic_err_t pmic_drv_set_vout(uint64_t reg_id, uint64_t voltage_uv) {
    // Look up regulator info
    bd71837_reg_t *regulator = &bd71837_regulator_table[reg_id];

    // sanity checks
    if (!regulator->reg.enabled) {
        LOG_PMIC_DRIVER_ERR("Cannot set voltage for a disabled regulator\n");
        return SDDF_PMIC_ERR_FAIL_REG;
    }
    if (!regulator->reg.capabilities.voltage.adjustable) {
        LOG_PMIC_DRIVER_ERR("Tried to set voltage for incompatible regulator %zu!\n", reg_id);
        return SDDF_PMIC_ERR_BAD_SETTING;
    }

    // check new voltage is valid
    pmic_unit_t max = regulator->reg.capabilities.voltage.max_value;
    pmic_unit_t min = regulator->reg.capabilities.voltage.min_value;
    if (voltage_uv >= max || voltage_uv <= min) {
        LOG_PMIC_DRIVER_ERR("Incompatible voltage requested!\n");
        return SDDF_PMIC_ERR_BAD_SETTING;
    }
    // prepare regulator register write
    // most registers simply require us to write to bits [quantisation:0], but some
    // are special cases
    uint8_t i2c_reg_val;
    if (reg_id == BD718XX_BUCK5) {
        return pmic_not_implemented();
    } else if (reg_id == BD718XX_LDO1) {
        return pmic_not_implemented();
    } else if (reg_id == BD718XX_LDO2) {
        return pmic_not_implemented();
    } else {
        // all other regulators
        uint64_t uv_range = max - min;
        uint64_t uv_per_step = uv_range / (1 << regulator->reg.capabilities.voltage.quantisation);

        uint64_t target_val = (voltage_uv - min) / uv_per_step;

        // If our target can't fit in the register, we've screwed up.
        LOG_PMIC_DRIVER("Setting voltage to %zu - target value = %zu\n", voltage_uv, target_val);
        assert(target_val <= (1 << regulator->reg.capabilities.voltage.quantisation));

        i2c_reg_val = (uint8_t) (target_val & 0xff);
    }

    // prepare i2c transaction
    i2c_data_region[0] = regulator->i2c_reg_addr;
    i2c_data_region[1] = i2c_reg_val;
    sddf_i2c_nb_write(&libi2c_conf, PMIC_I2C_ADDR, i2c_data_region, 2);
    // We set the state machine up in protected()
    return SDDF_PMIC_ERR_OK;
}

sddf_pmic_err_t pmic_drv_set_climit(uint64_t reg_id, uint64_t current_ua) {
    return pmic_not_implemented();
}

sddf_pmic_err_t pmic_drv_get_info(uint64_t reg_id, sddf_pmic_reg_info_t *info) {
    return pmic_not_implemented();
}


void init(void)
{
    // Setup i2c client connection
    assert(i2c_config_check_magic((void *)&i2c_config));
    i2c_data_region = (uint8_t *)i2c_config.data.vaddr;
    queue = i2c_queue_init(i2c_config.virt.req_queue.vaddr, i2c_config.virt.resp_queue.vaddr);

    bool claimed = i2c_bus_claim(i2c_config.virt.id, PMIC_I2C_ADDR);
    if (!claimed) {
        LOG_PMIC_DRIVER_ERR("Failed to claim PMIC bus address! Dying now!\n");
        assert(false);
    }

    /* Initialise libi2c */
    libi2c_init(&libi2c_conf, &queue);

    pmic_reset_state(&state);
    LOG_PMIC_DRIVER("Initialised.\n");
}

void notified(microkit_channel ch)
{
    if (ch == i2c_config.virt.id) {
        if (state.curr_ppc_op == SDDF_PMIC_PPC_INVALID) {
            LOG_PMIC_DRIVER_ERR("Spurious I2C interrupt!\n");
            return;
        }
        // Simply report if we failed to complete.
        i2c_addr_t returned_addr;
        size_t err_cmd_idx = 0;
        int ret = sddf_i2c_nb_return(&libi2c_conf, &returned_addr, &err_cmd_idx);

        if (ret == I2C_ERR_OK) {
            LOG_PMIC_DRIVER("Completed request for client %u. Opcode = %zu\n", state.curr_client, state.curr_ppc_op);
        } else {
            LOG_PMIC_DRIVER_ERR("I2C request failed for client %u! Opcode = %zu\n", state.curr_client, state.curr_ppc_op);
        }

        // Clean up state for next request.
        pmic_reset_state(&state);
    } else {
        LOG_PMIC_DRIVER_ERR("Unknown channel 0x%x!\n", ch);
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    sddf_pmic_err_t err = 0;
    uint64_t ret_num = 0;
    uint32_t argc = microkit_msginfo_get_count(msginfo);
    // Due to our HACK to support I2C, there exists a race condition on repeated calls to
    // this driver. If we're currently waiting for an I2C response, simply reject any PPC.
    if (state.curr_ppc_op != SDDF_PMIC_PPC_INVALID) {
        LOG_PMIC_DRIVER_ERR("Rejecting incoming PPC due to outstanding request! Try again soon...\n");
        err = SDDF_PMIC_ERR_BUSY;
        return microkit_msginfo_new(err, 1);
    }
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_PMIC_ENABLE_REG: {
        if (argc != 1) {
            LOG_PMIC_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
                err = SDDF_PMIC_ERR_BAD_PPC_CALL;
            break;
        }
        uint32_t reg_id = (uint32_t)microkit_mr_get(SDDF_PMIC_ENABLE_REG_REG_ID);
        LOG_PMIC_DRIVER("get request pmic_enable_reg(%d)\n", reg_id);
        state.err = pmic_drv_enable_reg(reg_id);
        break;
    }
    case SDDF_PMIC_DISABLE_REG: {
        if (argc != 1) {
            LOG_PMIC_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = SDDF_PMIC_ERR_BAD_PPC_CALL;
            break;
        }
        uint32_t reg_id = (uint32_t)microkit_mr_get(SDDF_PMIC_DISABLE_REG_REG_ID);
        LOG_PMIC_DRIVER("get request pmic_disable_reg(%d)\n", reg_id);
        state.err = pmic_drv_disable_reg(reg_id);
        break;
    }
    case SDDF_PMIC_SET_VOUT: {
        if (argc != 3) {
            LOG_PMIC_DRIVER_ERR("Incorrect number of arguments %u != 3\n", argc);
            err = SDDF_PMIC_ERR_BAD_PPC_CALL;
            break;
        }
        uint32_t reg_id = (uint32_t)microkit_mr_get(SDDF_PMIC_SET_VOUT_REG_ID);
        uint64_t voltage_uv = microkit_mr_get(SDDF_PMIC_SET_VOUT_VOLTAGE_UV);
        uint32_t op_mode_id = (uint32_t)microkit_mr_get(SDDF_PMIC_SET_VOUT_OP_MODE_ID);
        LOG_PMIC_DRIVER("get request pmic_set_vout(%d, %lu, %d)\n", reg_id, voltage_uv, op_mode_id);
        state.err = pmic_drv_set_vout(reg_id, voltage_uv);
        break;
    }
    case SDDF_PMIC_SET_CLIMIT: {
        if (argc != 3) {
            LOG_PMIC_DRIVER_ERR("Incorrect number of arguments %u != 3\n", argc);
            err = SDDF_PMIC_ERR_BAD_PPC_CALL;
            break;
        }
        uint32_t reg_id = (uint32_t)microkit_mr_get(SDDF_PMIC_SET_CLIMIT_REG_ID);
        uint64_t current_ua = microkit_mr_get(SDDF_PMIC_SET_CLIMIT_CURRENT_UA);
        uint32_t op_mode_id = (uint32_t)microkit_mr_get(SDDF_PMIC_SET_CLIMIT_OP_MODE_ID);
        LOG_PMIC_DRIVER("get request pmic_set_climit(%d, %lu, %d)\n", reg_id, current_ua, op_mode_id);
        state.err = pmic_drv_set_climit(reg_id, current_ua);
        break;
    }
    case SDDF_PMIC_GET_REG_INFO: {
        if (argc != 1) {
            LOG_PMIC_DRIVER_ERR("Incorrect number of arguments %u != 1\n", argc);
            err = SDDF_PMIC_ERR_BAD_PPC_CALL;
            break;
        }
        uint32_t reg_id = (uint32_t)microkit_mr_get(SDDF_PMIC_GET_REG_INFO_REG_ID);
        sddf_pmic_reg_info_t info = {0};
        LOG_PMIC_DRIVER("get request pmic_get_reg_info(%d)\n", reg_id);
        state.err = pmic_drv_get_info(reg_id, &info);
        if (err == SDDF_PMIC_GET_REG_INFO_SUCCESS) {
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_ENABLED, info.enabled);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_VOLTAGE_UV, info.voltage_uv);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_CURRENT_UA, info.current_ua);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_MIN_VOLTAGE_UV, info.min_voltage_uv);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_MAX_VOLTAGE_UV, info.max_voltage_uv);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_MIN_CURRENT_UA, info.min_current_ua);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_MAX_CURRENT_UA, info.max_current_ua);
            microkit_mr_set(SDDF_PMIC_GET_REG_INFO_RAMPRATE, info.ramprate);
            ret_num = 9; /* MR0-MR8 */
        }
        break;
    }
    default:
        LOG_PMIC_DRIVER_ERR("Unknown request %lu to PMIC driver from channel %u\n",
                       microkit_msginfo_get_label(msginfo), ch);
        err = SDDF_PMIC_ERR_BAD_PPC_CALL;
    }
    if (state.err != SDDF_PMIC_ERR_OK) {
        // Give up and die if we failed to set up a valid op
        err = state.err;
    } else {
        // We didn't explode, proceed to sleep for i2c operation.
        // Per the HACK label earlier, we pre-emptively return a success
        // to clients here!
        LOG_PMIC_DRIVER("Preparing to sleep for i2c return...\n");
    }

    return microkit_msginfo_new(err, ret_num);
}

