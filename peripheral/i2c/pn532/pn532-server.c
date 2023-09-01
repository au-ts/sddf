/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// pn532-server.c
// Simple server for interacting with the pn532 driver. Exposes PPC
// interface for getting most recent UID from Mifare Classic cards.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 09/2023

#include <sel4cp.h>
#include <sel4.h>
#include "printf.h"

static uint8_t uid[7] = {0,0,0,0,0,0,0};
const uint8_t pn53x_ack_frame[] = { 0x00, 0x00, 0xff, 0x00, 0xff, 0x00 };
const uint8_t pn53x_nack_frame[] = { 0x00, 0x00, 0xff, 0xff, 0x00, 0x00 };
static const uint8_t pn53x_error_frame[] = { 0x00, 0x00, 0xff, 0x01, 0xff, 0x7f, 0x81, 0x00 };
const uint8_t pn532_i2c_address = 0x48 >> 1;


static inline void pn532_init(void) {
    // Set up device parameters
    uint8_t params = PARAM_AUTO_ATR_RES | PARAM_AUTO_RATS;
    
}

void init(void) {
    sel4cp_dbg_puts("pn532: init\n");
}

void poll_loop(void) {
    
    while (1) {


        
        seL4_Yield();
    }

    
}

void notified(sel4cp_channel c) {
    switch (c) {
     
        default:
            sel4cp_dbg_puts("pn532: unknown notification\n");
            break;
    }
}

/**
 * Returns the most recent UID
*/
seL4_MessageInfo_t protected(sel4cp_channel c, seL4_MessageInfo_t m) {
    // uint64_t arg1 = sel4cp_mr_get(0);   // Bus
    // uint64_t arg2 = sel4cp_mr_get(1);   // Address
    for (int i = 0; i < 7; i++) {
        sel4cp_mr_set(i, uid[i]);
    }

    return sel4cp_msginfo_new(0, 7);
}