/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/util/printf.h>


/*
    For a first cut this example will be configured as loopback and should just periodically (say once per second) send some message (with a tag
    indicating this is a transmit) and then read the message (again tagged to indicate rx).

*/

void init(void) {
    microkit_dbg_puts("Example started! BEEP BEEP BEEP TESTING SHELL SCRIPT!\n");
}

void notified(microkit_channel ch) {
    microkit_dbg_puts("Interrupt received!\n");
    ;
}