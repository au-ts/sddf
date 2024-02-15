/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c-transport.c
// Transport layer for sDDF i2c drivers. Manages all shared ring buffers.
// This module is imported by both the driver and server. Note that we expect
// the server to be responsible for initialising the buffers.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#include <string.h>
#include <sddf/util/printf.h>
#include <sddf/i2c/transport.h>
#include "driver.h"
#include "i2c.h"

// Shared memory regions
uintptr_t req_free;
uintptr_t req_used;
uintptr_t ret_free;
uintptr_t ret_used;
uintptr_t driver_bufs;

ring_handle_t req_ring;
ring_handle_t ret_ring;

void i2cTransportInit(int buffer_init) {
    microkit_dbg_puts("Initialising i2c transport layer => ");
    if (buffer_init) {
        microkit_dbg_puts("Initialising buffers\n");
    } else {
        microkit_dbg_puts("Not initialising buffers\n");
    }
    // Initialise rings
    ring_init(&req_ring, (ring_buffer_t *) req_free, (ring_buffer_t *) req_used, buffer_init);
    ring_init(&ret_ring, (ring_buffer_t *) ret_free, (ring_buffer_t *) ret_used, buffer_init);

    // If the caller is initialising, also populate the free buffers.
    // Since all buffers are back to back in memory, need to offset each ring's buffers
    // NOTE: To extend this code for more than 2 i2c masters the memory mapping will need to be adjusted.
    if (buffer_init) {
        for (int i = 0; i < I2C_BUF_COUNT; i++) {
            // TODO: check buffer offsetting here. This is definitely too sparse because I haven't updated
            //       it form the 4-buf design
            enqueue_free(&req_ring, (uintptr_t) driver_bufs + (i * I2C_BUF_SIZE), I2C_BUF_SIZE);
            enqueue_free(&ret_ring, (uintptr_t) driver_bufs + (I2C_BUF_SIZE * (i + I2C_BUF_COUNT)), I2C_BUF_SIZE);
        }
    }

}


req_buf_ptr_t allocReqBuf(size_t size, uint8_t *data, uint8_t client, uint8_t addr) {
    // microkit_dbg_puts("transport: Allocating request buffer\n")
    if (size > I2C_BUF_SIZE - REQ_BUF_DATA_OFFSET*sizeof(i2c_token_t)) {
        printf("transport: Requested buffer size %zu too large\n", size);
        return 0;
    }

    // Allocate a buffer from the appropriate ring
    uintptr_t buf;
    unsigned int sz;
    int ret = dequeue_free(&req_ring, &buf, &sz);
    if (ret != 0) {
        return 0;
    }

    // Load the client ID and i2c address into first two bytes of buffer
    ((uint8_t *) buf)[REQ_BUF_CLIENT] = client;
    ((uint8_t *) buf)[REQ_BUF_ADDR] = addr;
    const uint8_t sz_offset = REQ_BUF_DATA_OFFSET*sizeof(uint8_t);


    // Copy the data into the buffer
    memcpy((void *) buf + sz_offset, data, size);

    // Enqueue the buffer
    ret = enqueue_used(&req_ring, buf, size + sz_offset);
    printf("transport: Allocated request buffer %p storing %u bytes\n", buf, size);
    if (ret != 0) {
        enqueue_free(&req_ring, buf, I2C_BUF_SIZE);
        return 0;
    }

    return (req_buf_ptr_t)buf;
}

ret_buf_ptr_t getRetBuf() {
    // microkit_dbg_puts("transport: Getting return buffer\n");

    // Allocate a buffer from the appropriate ring
    uintptr_t buf;
    unsigned int sz;
    int ret = dequeue_free(&ret_ring, &buf, &sz);
    if (ret != 0) {
        microkit_dbg_puts("transport: Failed to get return buffer due to empty free ring!\n");
        return 0;
    }
    printf("transport: Got return buffer %p\n", buf);
    return (ret_buf_ptr_t)buf;
}

int pushRetBuf(ret_buf_ptr_t buf, size_t size) {
    microkit_dbg_puts("transport: pushing return buffer\n");
    if (size > I2C_BUF_SIZE || !buf) {
        return 0;
    }

    // Enqueue the buffer
    int ret = enqueue_used(&ret_ring, (uintptr_t)buf, size);
    if (ret != 0) {
        return 0;
    }
    return -1;
}

static inline uintptr_t popBuf(ring_handle_t *ring, size_t *sz) {
    uintptr_t buf;
    int ret = dequeue_used(ring, ((uintptr_t*)&buf), (unsigned *)sz);
    printf("Popping buffer containing %zu bytes\n", *sz);
    if (ret != 0) return 0;
    return buf;
}

req_buf_ptr_t popReqBuf(size_t *size) {
    // microkit_dbg_puts("transport: popping request buffer\n");

    // Allocate a buffer from the appropriate ring
    return (req_buf_ptr_t) popBuf(&req_ring, size);
}


ret_buf_ptr_t popRetBuf(size_t *size) {
    // microkit_dbg_puts("transport: popping return buffer\n");

    // Allocate a buffer from the appropriate ring
    return (ret_buf_ptr_t) popBuf(&ret_ring, size);
}

int retBufEmpty(void) {
    return ring_empty(ret_ring.used_ring);
}

int releaseReqBuf(req_buf_ptr_t buf) {
    // microkit_dbg_puts("transport: releasing request buffer\n");

    if (!buf) {
        return 0;
    }

    // Enqueue the buffer
    int ret = enqueue_free(&req_ring, (uintptr_t)buf, I2C_BUF_SIZE);
    if (ret != 0) {
        return 0;
    }
    return -1;
}

int releaseRetBuf(ret_buf_ptr_t buf) {
    // microkit_dbg_puts("transport: releasing return buffer\n");

    if (!buf) {
        return 0;
    }

    // Enqueue the buffer
    int ret = enqueue_free(&ret_ring, (uintptr_t)buf, I2C_BUF_SIZE);
    if (ret != 0) {
        return 0;
    }
    return -1;
}
