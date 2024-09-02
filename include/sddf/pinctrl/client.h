/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/pinctrl/protocol.h>

/**
 * Reset the I/O mux controller to default values in DTS via PPC into the passive pinctrl driver.
 * Use the label to indicate this request.
 * @param microkit channel of pinctrl driver.
 */
static inline sddf_pinctrl_response_t sddf_pinctrl_reset(microkit_channel channel)
{
    microkit_msginfo resp = microkit_ppcall(channel, microkit_msginfo_new(SDDF_PINCTRL_RESET, 0));
    
    return ((sddf_pinctrl_response_t) microkit_msginfo_get_label(resp));
}

/**
 * Read a value from a pinmux register via PPC into the passive pinctrl driver.
 * Use the label to indicate this request.
 * @param microkit channel of pinctrl driver.
 * @param reg_offset offset of the desired register from the device base physical address.
 * @param ret_val if the return value is a success, the register value in the device is written to this pointer.
 */
static inline sddf_pinctrl_response_t sddf_pinctrl_read_mux(microkit_channel channel, uint32_t reg_offset, uint32_t *ret_val)
{
    microkit_mr_set(READ_MUX_REQ_OFFSET, reg_offset);

    microkit_msginfo resp = microkit_ppcall(channel, microkit_msginfo_new(SDDF_PINCTRL_READ_MUX, READ_MUX_REQ_NUM_ARGS));
    sddf_pinctrl_response_t status = (sddf_pinctrl_response_t) microkit_msginfo_get_label(resp);

    if (status == SDDF_PINCTRL_SUCCESS) {
        *ret_val = (uint32_t) microkit_mr_get(READ_MUX_RESP_VALUE);
    }

    return status;
}

/**
 * Query the pinmux register value that was written to memory when the driver initialised.
 * It won't necessarily be the same as the value in the Device Tree, see SION and "Quirky input registers" handling in the driver.
 * Use the label to indicate this request.
 * @param microkit channel of pinctrl driver.
 * @param reg_offset offset of the desired register from the device base physical address.
 * @param ret_val if the return value is a success, the register value in the device tree is written to this pointer.
 */
static inline sddf_pinctrl_response_t sddf_pinctrl_query_dts(microkit_channel channel, uint32_t reg_offset, uint32_t *ret_val)
{
    microkit_mr_set(QUERY_DTS_REQ_OFFSET, reg_offset);

    microkit_msginfo resp = microkit_ppcall(channel, microkit_msginfo_new(SDDF_PINCTRL_QUERY_DTS, QUERY_DTS_REQ_NUM_ARGS));
    sddf_pinctrl_response_t status = (sddf_pinctrl_response_t) microkit_msginfo_get_label(resp);

    if (status == SDDF_PINCTRL_SUCCESS) {
        *ret_val = (uint32_t) microkit_mr_get(QUERY_DTS_RESP_VALUE);
    }

    return status;
}
