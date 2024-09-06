/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Shared functionality/definitions between pinctrl drivers and clients */

enum sddf_pinctrl_request_label {
    SDDF_PINCTRL_RESERVED = 0,
    SDDF_PINCTRL_READ_MUX,
};

enum read_mux_request_ipc_index {
    READ_MUX_REQ_OFFSET = 0,
    READ_MUX_REQ_NUM_ARGS,
};

enum read_mux_reponse_ipc_index {
    READ_MUX_RESP_VALUE = 0,
    READ_MUX_RESP_NUM_RESULTS,
};

enum sddf_pinctrl_request_response_label {
    SDDF_PINCTRL_SUCCESS = 0,
    SDDF_PINCTRL_UNKNOWN_REQ,
    SDDF_PINCTRL_INVALID_ARGS,
};

typedef enum sddf_pinctrl_request_response_label sddf_pinctrl_response_t;
