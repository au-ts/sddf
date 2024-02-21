/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c.c
// Server for the i2c driver. Responsible for managing device security and multiplexing.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/i2c/i2c.h>
#include <sddf/i2c/transport.h>
#include <sddf/i2c/shared_ringbuffer.h>
#include "i2c.h"

#ifndef I2C_BUS_NUM
#error "I2C_BUS_NUM must be defined!"
#endif

// Security list: owner of each i2c address on the bus
i2c_security_list_t security_list[I2C_SECURITY_LIST_SZ];

/**
 * Main entrypoint for server.
*/
void init(void) {
    microkit_dbg_puts("I2C server init\n");
    i2cTransportInit(1);

    // Clear security list
    for (int j = 0; j < I2C_SECURITY_LIST_SZ; j++) {
        security_list[j] = -1;
    }
}

/**
 * Handler for notification from the driver. Driver notifies when
 * there is data to retrieve from the return path.
*/
static inline void driverNotify(void) {
    printf("server: Notified by driver!\n");
    // Read the return buffer
    if (retBufEmpty()) {
        return;
    }
    size_t sz;
    ret_buf_ptr_t ret = popRetBuf(&sz);
    if (ret == 0) {
        return;
    }
    printf("ret buf first 4 bytes: %x %x %x %x\n", ret[0], ret[1], ret[2], ret[3]);
    // printf("server: Got return buffer %p\n", ret);
    printf("bus = %i client = %i addr = %i sz=%u\n", *(uint8_t *) ret,
    *(uint8_t *) (ret + sizeof(uint8_t)), *(uint8_t *) (ret + 2*sizeof(uint8_t)),
    sz);

    uint8_t err = ret[RET_BUF_ERR];
    // uint8_t err_tk = ret[RET_BUF_ERR_TK];
    uint8_t client = ret[RET_BUF_CLIENT];
    uint8_t addr = ret[RET_BUF_ADDR];

    if (err) {
        printf("server: Error %i on bus %i for client %i at token of type %i\n", err, I2C_BUS_NUM, client, addr);
    } else {
        printf("server: Success on bus %i for client %i at address %i\n", I2C_BUS_NUM, client, addr);

        // TODO: logic here to return
    }

    releaseRetBuf(ret);
}

static inline void clientNotify(int channel) {
    // 
}

void notified(microkit_channel c) {
    switch (c) {
        case DRIVER_NOTIFY_ID:
            driverNotify();
            break;
        case 2:
            break;
    }
}

static inline seL4_MessageInfo_t ppcError(void) {
    microkit_mr_set(0, -1);
    return microkit_msginfo_new(0, 1);
}

/**
 * Claim an address on a bus.
*/
static inline seL4_MessageInfo_t securityClaim(uint8_t addr, uint64_t client) {
    // Check that the address is not already claimed

    if (security_list[addr] != -1) {
        microkit_dbg_puts("I2C|ERROR: Address already claimed!\n");
        return ppcError();
    }

    // Claim
    security_list[addr] = client;
    microkit_mr_set(0, 0);
    return microkit_msginfo_new(0, 1);
}

/**
 * Release an address on a bus.
*/
static inline seL4_MessageInfo_t securityRelease(uint8_t addr, uint64_t client) {
    // Check that the address is claimed by the client
    if (security_list[addr] != client) {
        microkit_dbg_puts("I2C|ERROR: Address not claimed by client!\n");
        return ppcError();
    }

    // Release
    security_list[addr] = -1;
    microkit_mr_set(0, 0);
    return microkit_msginfo_new(0, 1);
}

/**
 * Protected procedure calls into this server are used managing the security lists.
*/
seL4_MessageInfo_t protected(microkit_channel c, seL4_MessageInfo_t m) {
    // Determine the type of request
    size_t req = microkit_mr_get(I2C_PPC_MR_REQTYPE);
    size_t ppc_addr = microkit_mr_get(I2C_PPC_MR_ADDR);
    size_t client_pd = microkit_mr_get(I2C_PPC_MR_CID);

    // Check arguments are valid
    if (req != I2C_PPC_CLAIM || req != I2C_PPC_RELEASE) {
        microkit_dbg_puts("I2C|ERROR: Invalid PPC request type!\n");
        return ppcError();
    }
    if (ppc_addr < 0 || ppc_addr > 127) {
        microkit_dbg_puts("I2C|ERROR: Invalid i2c address in PPC!\n");
        return ppcError();
    }

    switch (req) {
        case I2C_PPC_CLAIM:
            // Claim an address
            return securityClaim(ppc_addr, client_pd);
        case I2C_PPC_RELEASE:
            // Release an address
            return securityRelease(ppc_addr, client_pd);
    }

    return microkit_msginfo_new(0, 7);
}
