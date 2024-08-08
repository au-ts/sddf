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
 * Set a pinmux value in the I/O mux controller via PPC into the passive pinctrl driver.
 * Use the label to indicate this request.
 * @param microkit channel of pinctrl driver.
 * @param reg_offset offset of the desired register from the device base physical address.
 * @param reg_val desired value to write to the register.
 */
static inline bool sddf_pinctrl_set_mux(microkit_channel channel, uint32_t reg_offset, uint32_t reg_val)
{
    microkit_mr_set(REGISTER_OFFSET_WORD, reg_offset);
    microkit_mr_set(REGISTER_VALUE_WORD, reg_val);
    microkit_ppcall(channel, microkit_msginfo_new(SDDF_PINCTRL_SET_MUX, 2));

    return microkit_mr_get(0) > 0;
}
