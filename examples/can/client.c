/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>

void init(void) {
    microkit_dbg_puts("Example started! BEEP BEEP BEEP TESTING SHELL SCRIPT!\n");
}

void notified(microkit_channel ch) {
    microkit_dbg_puts("Interrupt received!\n");
    ;
}