/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/i2c/queue.h>

i2c_queue_handle_t i2c_queue_init(i2c_queue_t *request, i2c_queue_t *response)
{
    i2c_queue_handle_t handle;
    handle.request = request;
    handle.response = response;

    return handle;
}
