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
#include "i2c-driver.h"
#include "i2c-token.h"
#include "sw_shared_ringbuffer.h"
#include "printf.h"
#include "i2c-transport.h"
#include "i2c.h"



// Security lists: one for each possible bus.
i2c_security_list_t security_list0[I2C_SECURITY_LIST_SZ];
i2c_security_list_t security_list1[I2C_SECURITY_LIST_SZ];
i2c_security_list_t security_list2[I2C_SECURITY_LIST_SZ];
i2c_security_list_t security_list3[I2C_SECURITY_LIST_SZ];

static inline void testds3231() {
    uint8_t addr = 0x68;
    uint8_t cid = 1;

    i2c_token_t request[10] = {
        I2C_TK_START,
        I2C_TK_ADDRW,
        I2C_TK_DAT,
        0x6,        //  Year register
        I2C_TK_DAT,
        0x20,
        I2C_TK_DAT,
        0x24,
        I2C_TK_STOP,
        I2C_TK_END,
    };
    req_buf_ptr_t ret = allocReqBuf(2, 10, request, cid, addr);
    if (!ret) {
        sel4cp_dbg_puts("test: failed to allocate req buffer\n");
        return;
    }
    sel4cp_notify(DRIVER_NOTIFY_ID);

    // Try read back
    i2c_token_t request2[10] = {
        I2C_TK_START,
        I2C_TK_ADDRW,
        I2C_TK_DAT,
        0x6,
        I2C_TK_START,
        I2C_TK_ADDRR,
        I2C_TK_DAT,
        I2C_TK_DATA_END,
        I2C_TK_STOP,
        I2C_TK_END,
    };
    ret = allocReqBuf(2, 10, request2, cid, addr);
    if (!ret) {
        sel4cp_dbg_puts("test: failed to allocate req buffer\n");
        return;
    }
    sel4cp_notify(DRIVER_NOTIFY_ID);
}

static inline void test() {
    uint8_t cid = 1; // client id
    uint8_t addr = 0x24; // address
    i2c_token_t request[11] = {
        I2C_TK_START,
        I2C_TK_ADDRR,
        I2C_TK_DAT,
        0x01,
        I2C_TK_DAT,
        0x02,
        I2C_TK_DAT,
        0x03,
        I2C_TK_DATA_END,
        I2C_TK_STOP,
        I2C_TK_END,
    };
    // sel4cp_dbg_puts("test: allocating req buffer\n");
    // Write 1,2,3 to address 0x20
    // req_buf_ptr_t ret = allocReqBuf(2, 11, request, cid, addr);
    // if (!ret) {
    //     sel4cp_dbg_puts("test: failed to allocate req buffer\n");
    //     return;
    // }
    // sel4cp_notify(DRIVER_NOTIFY_ID);

    addr = 0x24; // address
    i2c_token_t request2[10] = {
        I2C_TK_START,
        I2C_TK_ADDRW,
        I2C_TK_DAT,
        0x03,
        I2C_TK_DAT,
        0x02,
        I2C_TK_DAT,
        0x01,
        I2C_TK_STOP,
        I2C_TK_END,
    };
    // Write 1,2,3 to address 0x20
    req_buf_ptr_t ret = allocReqBuf(2, 10, request2, cid, addr);
    if (!ret) {
        sel4cp_dbg_puts("test: failed to allocate req buffer\n");
        return;
    }
    sel4cp_notify(DRIVER_NOTIFY_ID);
    
    ret = allocReqBuf(2, 11, request, cid, addr);
    if (!ret) {
        sel4cp_dbg_puts("test: failed to allocate req buffer\n");
        return;
    }
    sel4cp_notify(DRIVER_NOTIFY_ID);
    
    ret = allocReqBuf(2, 10, request2, cid, addr);
    if (!ret) {
        sel4cp_dbg_puts("test: failed to allocate req buffer\n");
        return;
    }
    sel4cp_notify(DRIVER_NOTIFY_ID);
}

static inline void testLong() {
    uint8_t cid = 1; // client id
    uint8_t addr = 0x68; // address
    i2c_token_t request[64] = {
        I2C_TK_START,
        I2C_TK_ADDRW,
        I2C_TK_DAT,
        0x06,
        I2C_TK_DAT,
        0x01,
        I2C_TK_DAT,
        0x02,
        I2C_TK_DAT,
        0x03,
        I2C_TK_DAT,
        0x04,
        I2C_TK_DAT,
        0x05,
        I2C_TK_DAT,
        0x06,
        I2C_TK_DAT,
        0x07,
        I2C_TK_DAT,
        0x08,
        I2C_TK_DAT,
        0x09,
        I2C_TK_DAT,
        0x0A,
        I2C_TK_DAT,
        0x0B,
        I2C_TK_DAT,
        0x0C,
        I2C_TK_DAT,
        0x0D,
        I2C_TK_DAT,
        0x0E,
        I2C_TK_DAT,
        0x0F,
        I2C_TK_DAT,
        0x10,
        I2C_TK_DAT,
        0x12,
        I2C_TK_DAT,
        0x13,
        I2C_TK_DAT,
        0x14,
        I2C_TK_DAT,
        0x15,
        I2C_TK_DAT,
        0x16,
        I2C_TK_DAT,
        0x17,
        I2C_TK_DAT,
        0x18,
        I2C_TK_DAT,
        0x19,
        I2C_TK_DAT,
        0x1A,
        I2C_TK_DAT,
        0x1B,
        I2C_TK_DAT,
        0x1C,
        I2C_TK_DAT,
        0x1D,
        I2C_TK_DAT,
        0x1E,
        I2C_TK_STOP,
        I2C_TK_END,
    };
    req_buf_ptr_t ret = allocReqBuf(2, 64, request, cid, addr);
    if (!ret) {
        sel4cp_dbg_puts("test: failed to allocate req buffer\n");
        return;
    }
    sel4cp_notify(DRIVER_NOTIFY_ID);
}

/**
 * Main entrypoint for server.
*/
void init(void) {
    sel4cp_dbg_puts("I2C server init\n");
    i2cTransportInit(1);
    // Clear security lists
    for (int i = 0; i < I2C_SECURITY_LIST_SZ; i++) {
        security_list0[i] = 0;
        security_list1[i] = 0;
        security_list2[i] = 0;
        security_list3[i] = 0;
    }

    // test();
    testds3231();
    // testLong();
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
        size_t *sz;
        ret_buf_ptr_t ret = popRetBuf(i, &sz);
        printf("ret buf first 4 bytes: %x %x %x %x\n", ret[0], ret[1], ret[2], ret[3]);
        printf("server: Got return buffer %p\n", ret);
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
        }

        releaseRetBuf(i, ret);
    }
}


void notified(sel4cp_channel c) {
    switch (c) {
        case DRIVER_NOTIFY_ID:
            driverNotify();
            break;
        case 2:
            // Client 1
            break;
    }
}

/**
 * Protected procedure calls into this server are used managing the security lists. 
*/
seL4_MessageInfo_t protected(sel4cp_channel c, seL4_MessageInfo_t m) {
    // Determine the type of request
    uint64_t req = sel4cp_mr_get(I2C_PPC_REQTYPE);
    uint64_t arg1 = sel4cp_mr_get(1);   // Bus
    uint64_t arg2 = sel4cp_mr_get(2);   // Address
    switch (req) {
        case I2C_PPC_CLAIM:
            // Claim an address
            break;
        case I2C_PPC_RELEASE:
            // Release an address
            break;
    }

    return sel4cp_msginfo_new(0, 0);
}