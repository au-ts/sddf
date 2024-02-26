/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/i2c/queue.h>

void i2c_queue_init(i2c_queue_handle_t *h, i2c_queue_t *request, i2c_queue_t *response)
{
    h->request = request;
    h->response = response;
}
