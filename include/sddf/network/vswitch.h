/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Vswitch operation status codes */
typedef enum {
    /* no error */
    VSWITCH_ERR_OKAY = 0,
    /* Invalid IP address provided */
    VSWITCH_ERR_INVALID_IP,
    /* Client does not have correct permissions */
    VSWITCH_ERR_OPERATION_DENIED,
    /* Queried client has not yet registered an IP address */
    VSWITCH_ERR_NO_IP,
    /* Queried client does not have an IP address (virtualiser port) */
    VSWITCH_ERR_VIRT_PORT,
    /* Unsupported operation */
    VSWITCH_ERR_INVALID_OPERATION,
} vswitch_err_t;

/**
 * Register a client's IP address with the vswitch.
 */
#define VSWITCH_SET_IP_ADDR 0

typedef enum {
    /* IP address to register */
    VSWITCH_SET_IP_ADDR_ARG = 0,
    /* Number of arguments */
    VSWITCH_SET_NUM_ARGS,
} vswitch_set_args_t;

typedef enum {
    /* Success of operation */
    VSWITCH_SET_RET_ERR = 0,
    /* Number of return arguments */
    VSWITCH_SET_RET_NUM_ARGS,
} vswitch_set_ret_args_t;

/**
 * Request a client's vswitch ID and reachable neighbours.
 */
#define VSWITCH_QUERY_STATE 1

typedef enum {
    /* Number of arguments */
    VSWITCH_QUERY_NUM_ARGS = 0,
} vswitch_query_args_t;

typedef enum {
    /* Success of operation */
    VSWITCH_QUERY_RET_ERR = 0,
    /* Vswitch client ID of caller */
    VSWITCH_QUERY_RET_CLIENT_ID,
    /* Bitmap of client IDs caller can reach */
    VSWITCH_QUERY_RET_REACHABLE_BITMAP,
    /* Number of return arguments */
    VSWITCH_QUERY_RET_NUM_ARGS,
} vswitch_query_ret_args_t;

/**
 * Request another client's IP address.
 */
#define VSWITCH_REQ_CLIENT 2

typedef enum {
    /* Client ID to query IP address */
    VSWITCH_REQ_CLIENT_ID = 0,
    /* Number of arguments */
    VSWITCH_REQ_NUM_ARGS,
} vswitch_req_args_t;

typedef enum {
    /* Success of operation */
    VSWITCH_REQ_RET_ERR = 0,
    /* Vswitch client ID of caller */
    VSWITCH_REQ_RET_IP_ADDR,
    /* Number of return arguments */
    VSWITCH_REQ_RET_NUM_ARGS,
} vswitch_req_ret_args_t;
