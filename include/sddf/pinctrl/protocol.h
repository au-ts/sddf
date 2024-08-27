/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Shared functionality/definitions between pinctrl drivers and clients */

enum sddf_pinctrl_request_label {
    SDDF_PINCTRL_RESERVED = 0,
    SDDF_PINCTRL_SET_MUX,
    SDDF_PINCTRL_QUERY_DTS,
};


enum set_mux_request_ipc_index {
    SET_MUX_REQ_OFFSET = 0,
    SET_MUX_REQ_VALUE,
    SET_MUX_REQ_NUM_ARGS,
};

enum set_mux_reponse_ipc_index {
    SET_MUX_RESP_NUM_RESULTS = 0,
};


enum query_dts_request_ipc_index {
    QUERY_DTS_REQ_OFFSET = 0,
    QUERY_DTS_REQ_NUM_ARGS,
};

enum query_dts_reponse_ipc_index {
    QUERY_DTS_RESP_VALUE = 0,
    QUERY_DTS_RESP_NUM_RESULTS,
};


enum sddf_pinctrl_request_response_label {
    SDDF_PINCTRL_SUCCESS = 0,
    SDDF_PINCTRL_UNKNOWN_REQ,
    SDDF_PINCTRL_INVALID_ARGS,
    SDDF_PINCTRL_NOT_IN_DTS,
};

typedef enum sddf_pinctrl_request_response_label sddf_pinctrl_response_t;
