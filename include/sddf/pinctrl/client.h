/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <sddf/pinctrl/protocol.h>

#include <pinctrl_chips.h>

/**
 * Read a value from a pinmux register via PPC into the passive pinctrl driver.
 * Use the label to indicate this request.
 * @param channel of pinctrl driver.
 * @param reg_offset offset of the desired register from the device base physical address.
 * @param chip that the offset is relative to.
 * @param ret_val if the return value is a success, the register value in the device is written to this pointer.
 */
static inline sddf_pinctrl_response_t sddf_pinctrl_read_mux(microkit_channel channel, uint32_t reg_offset,
                                                            sddf_pinctrl_chip_idx_t chip, uint32_t *ret_val)
{
    microkit_mr_set(READ_MUX_REQ_OFFSET, reg_offset);
    microkit_mr_set(READ_MUX_REQ_CHIP_IDX, chip);

    microkit_msginfo resp = microkit_ppcall(channel,
                                            microkit_msginfo_new(SDDF_PINCTRL_READ_MUX, READ_MUX_REQ_NUM_ARGS));
    sddf_pinctrl_response_t status = (sddf_pinctrl_response_t)microkit_msginfo_get_label(resp);

    if (status == SDDF_PINCTRL_SUCCESS) {
        *ret_val = (uint32_t)microkit_mr_get(READ_MUX_RESP_VALUE);
    }

    return status;
}
