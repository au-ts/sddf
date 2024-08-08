/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Shared functionality/definitions between pinctrl drivers and clients */

enum ipc_index {
    REGISTER_OFFSET_WORD,
    REGISTER_VALUE_WORD
};

enum request_label {
    SDDF_PINCTRL_RESERVED,
    SDDF_PINCTRL_SET_MUX
};
