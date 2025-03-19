/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

void init(void) {
    sddf_printf("EXAMPLE STARTED!!!");
    sddf_printf("EXAMPLE STARTED!!!");
    sddf_printf("EXAMPLE STARTED!!!");
    sddf_printf("EXAMPLE STARTED!!!");
    sddf_printf("EXAMPLE STARTED!!!");
}

void notified(microkit_channel ch) {
    ;
}