/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c.c
// Server for the i2c driver. Responsible for managing device security and multiplexing.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#include <sel4cp.h>
#include <sel4/sel4.h>
#include "i2c-driver.h"
#include "i2c-token.h"
#include "sw_shared_ringbuffer.h"
#include "printf.h"
#include "i2c-transport.h"
#include "i2c.h"

// Security lists: one for each possible bus.
i2c_security_list_t security_list[I2C_NUM_BUSES][I2C_SECURITY_LIST_SZ];



/**
 * Main entrypoint for server.
*/
void init(void) {
    sel4cp_dbg_puts("I2C server init\n");
    i2cTransportInit(1);
    // Clear security lists
    for (int i = 0; i < I2C_SECURITY_LIST_SZ; i++) {
        for (int j = 0; j < I2C_NUM_BUSES; j++) {
            security_list[j][i] = -1;
        }
    }
}

/**
 * Handler for notification from the driver. Driver notifies when
 * there is data to retrieve from the return path.
*/
static inline void driverNotify(void) {
    printf("server: Notified by driver!\n");
    // Read the return buffer
    // No way to know which interface generated notification, so we just try all of them
    for (int i = 2; i < 4; i ++) {
        if (retBufEmpty(i)) {
            continue;
        }
        size_t sz;
        ret_buf_ptr_t ret = popRetBuf(i, &sz);
        if (ret == 0) {
            return;
        }
        printf("ret buf first 4 bytes: %x %x %x %x\n", ret[0], ret[1], ret[2], ret[3]);
        // printf("server: Got return buffer %p\n", ret);
        printf("bus = %i client = %i addr = %i sz=%u\n", *(uint8_t *) ret,
        *(uint8_t *) (ret + sizeof(uint8_t)), *(uint8_t *) (ret + 2*sizeof(uint8_t)),
        sz);

        uint8_t err = ret[RET_BUF_ERR];
        uint8_t err_tk = ret[RET_BUF_ERR_TK];
        uint8_t client = ret[RET_BUF_CLIENT];
        uint8_t addr = ret[RET_BUF_ADDR];

        if (err) {
            printf("server: Error %i on bus %i for client %i at token of type %i\n", err, i, client, addr);
        } else {
            printf("server: Success on bus %i for client %i at address %i\n", i, client, addr);

            // TODO: logic here to return
        }

        releaseRetBuf(i, ret);
    }
}


static inline void clientNotify(int channel) {

}


void notified(sel4cp_channel c) {
    switch (c) {
        case DRIVER_NOTIFY_ID:
            driverNotify();
            break;
        case 2:
            break;
    }
}

static inline seL4_MessageInfo_t ppcError(void) {
    sel4cp_mr_set(0, -1);
    return sel4cp_msginfo_new(0, 1);
}

/**
 * Claim an address on a bus.
*/
static inline seL4_MessageInfo_t securityClaim(int bus, uint8_t addr, uint64_t client) {
    // Check that the address is not already claimed
    i2c_security_list_t *list = security_list[bus];
    if (list[addr] != -1) {
        sel4_dbg_puts("I2C|ERROR: Address already claimed!\n");
        return ppcError();
    }

    // Claim
    list[addr] = client;
    sel4cp_mr_set(0, 0);
    return sel4cp_msginfo_new(0, 1);
}

/**
 * Release an address on a bus.
*/
static inline seL4_MessageInfo_t securityRelease(int bus, uint8_t addr, uint64_t client) {
    // Check that the address is claimed by the client
    i2c_security_list_t *list = security_list[bus];
    if (list[addr] != client) {
        sel4_dbg_puts("I2C|ERROR: Address not claimed by client!\n");
        return ppcError();
    }

    // Release
    list[addr] = -1;
    sel4cp_mr_set(0, 0);
    return sel4cp_msginfo_new(0, 1);
}



/**
 * Protected procedure calls into this server are used managing the security lists. 
*/
seL4_MessageInfo_t protected(sel4cp_channel c, seL4_MessageInfo_t m) {
    // Determine the type of request
    uint64_t req = sel4cp_mr_get(I2C_PPC_REQTYPE);
    uint64_t ppc_bus = sel4cp_mr_get(I2C_PPC_MR_BUS)
    uint64_t ppc_addr = sel4cp_mr_get(I2C_PPC_MR_ADDR);

    // Check arguments are valid
    if (req != I2C_PPC_CLAIM || req != I2C_PPC_RELEASE) {
        sel4_dbg_puts("I2C|ERROR: Invalid PPC request type!\n");
        return ppcError();
    }
    if (ppc_addr < 0 || ppc_addr > 127) {
        sel4_dbg_puts("I2C|ERROR: Invalid i2c address in PPC!\n");
        return ppcError();
    }
    if (ppc_bus < 2 || ppc_bus > 3) {
        sel4_dbg_puts("I2C|ERROR: Invalid i2c bus in PPC!\n");
        return ppcError();
    }

    switch (req) {
        case I2C_PPC_CLAIM:
            // Claim an address
            return securityClaim(ppc_bus, ppc_addr, c);
        case I2C_PPC_RELEASE:
            // Release an address
            return securityRelease(ppc_bus, ppc_addr, c);
    }

    return sel4cp_msginfo_new(0, 7);
}