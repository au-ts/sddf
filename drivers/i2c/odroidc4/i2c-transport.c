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

#include "i2c-driver.h"
#include "i2c-transport.h"
#include "printf.h"

// Shared memory regions
uintptr_t m2_req_free;
uintptr_t m2_req_used;
uintptr_t m3_req_free;
uintptr_t m3_req_used;

uintptr_t m2_ret_free;
uintptr_t m2_ret_used;
uintptr_t m3_ret_free;
uintptr_t m3_ret_used;
uintptr_t driver_bufs;

ring_handle_t m2ReqRing;
ring_handle_t m2RetRing;
ring_handle_t m3ReqRing;
ring_handle_t m3RetRing;


void _putchar(char character) {
    sel4cp_dbg_putc(character);
}

void i2cTransportInit(int buffer_init) {
    sel4cp_dbg_puts("Initialising i2c transport layer => ");
    if (buffer_init) {
        sel4cp_dbg_puts("Initialising buffers\n");
    } else {
        sel4cp_dbg_puts("Not initialising buffers\n");
    }
    // Initialise rings
    ring_init(&m2ReqRing, (ring_buffer_t *) m2_req_free, (ring_buffer_t *) m2_req_used, buffer_init);
    ring_init(&m2RetRing, (ring_buffer_t *) m2_ret_free, (ring_buffer_t *) m2_ret_used, buffer_init);
    ring_init(&m3ReqRing, (ring_buffer_t *) m3_req_free, (ring_buffer_t *) m3_req_used, buffer_init);
    ring_init(&m3RetRing, (ring_buffer_t *) m3_ret_free, (ring_buffer_t *) m3_ret_used, buffer_init);

    // If the caller is initialising, also populate the free buffers.
    // Since all buffers are back to back in memory, need to offset each ring's buffers
    // NOTE: To extend this code for more than 2 i2c masters the memory mapping will need to be adjusted.
    if (buffer_init) {
        for (int i = 0; i < I2C_BUF_COUNT; i++) {
            enqueue_free(&m2ReqRing, (uintptr_t) driver_bufs + (i * I2C_BUF_SZ), I2C_BUF_SZ);
            enqueue_free(&m2RetRing, (uintptr_t) driver_bufs + (I2C_BUF_SZ * (i + I2C_BUF_COUNT)), I2C_BUF_SZ);
            enqueue_free(&m3ReqRing, (uintptr_t) driver_bufs + (I2C_BUF_SZ * (i + 2 * I2C_BUF_COUNT)), I2C_BUF_SZ);
            enqueue_free(&m3RetRing, (uintptr_t) driver_bufs + (I2C_BUF_SZ * (i + 3 * I2C_BUF_COUNT)), I2C_BUF_SZ);
        }
    }

}


req_buf_ptr_t allocReqBuf(int bus, size_t size, uint8_t *data, uint8_t client, uint8_t addr) {
    // sel4cp_dbg_puts("transport: Allocating request buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }
    if (size > I2C_BUF_SZ - REQ_BUF_DAT_OFFSET*sizeof(i2c_token_t)) {
        printf("transport: Requested buffer size %zu too large\n", size);
        return 0;
    }
    
    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2ReqRing;
    } else {
        ring = &m3ReqRing;
    }
    uintptr_t buf;
    unsigned int sz;
    int ret = dequeue_free(ring, &buf, &sz);
    if (ret != 0) {
        return 0;
    }

    // Load the client ID and i2c address into first two bytes of buffer
    (uint8_t *) buf[REQ_BUF_CLIENT] = client;
    (uint8_t *) buf[REQ_BUF_ADDR] = addr;
    (uint8_t *) buf[REQ_BUF_BUS] = bus;
    const uint8_t sz_offset = REQ_BUF_DAT_OFFSET*sizeof(uint8_t);


    // Copy the data into the buffer
    memcpy((void *) buf + sz_offset, data, size);
    
    // Enqueue the buffer
    ret = enqueue_used(ring, buf, size + sz_offset);
    printf("transport: Allocated request buffer %p storing %u bytes\n", buf, size);
    if (ret != 0) {
        enqueue_free(ring, buf, I2C_BUF_SZ);
        return 0;
    }
    
    return buf;
}

ret_buf_ptr_t getRetBuf(int bus) {
    // sel4cp_dbg_puts("transport: Getting return buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }

    
    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2RetRing;
    } else {
        ring = &m3RetRing;
    }
    uintptr_t buf;
    unsigned int sz;
    int ret = dequeue_free(ring, &buf, &sz);
    if (ret != 0) {
        sel4cp_dbg_puts("transport: Failed to get return buffer due to empty free ring!\n");
        return 0;
    }
    printf("transport: Got return buffer %p\n", buf);
    return buf;
}

int pushRetBuf(int bus, ret_buf_ptr_t buf, size_t size) {
    // sel4cp_dbg_puts("transport: pushign return buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }
    if (size > I2C_BUF_SZ || !buf) {
        return 0;
    }
    
    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2RetRing;
    } else {
        ring = &m3RetRing;
    }

    // Enqueue the buffer
    int ret = enqueue_used(ring, (uintptr_t)buf, size);
    if (ret != 0) {
        return 0;
    }
    return -1;
}

static inline uintptr_t popBuf(ring_handle_t *ring, size_t *sz) {
    uintptr_t buf;
    int ret = dequeue_used(ring, &buf, sz);
    printf("Popping buffer containing %zu bytes\n", *sz);
    if (ret != 0) return 0;
    return buf;
} 

req_buf_ptr_t popReqBuf(int bus, size_t *size) {
    // sel4cp_dbg_puts("transport: popping request buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }

    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2ReqRing;
    } else {
        ring = &m3ReqRing;
    }
    return (req_buf_ptr_t) popBuf(ring, size);
}


ret_buf_ptr_t popRetBuf(int bus, size_t *size) {
    // sel4cp_dbg_puts("transport: popping return buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }

    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2RetRing;
    } else {
        ring = &m3RetRing;
    }
    return (ret_buf_ptr_t) popBuf(ring, size);
}

int retBufEmpty(int bus) {
    if (bus != 2 && bus != 3) {
        return 0;
    }

    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2RetRing;
    } else {
        ring = &m3RetRing;
    }
    return ring_empty(ring->used_ring);
}

int reqBufEmpty(int bus) {
    if (bus != 2 && bus != 3) {
        sel4cp_dbg_puts("transport: invalid bus requested on reqBufEmpty\n");
        return 0;
    }

    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2ReqRing;
    } else {
        ring = &m3ReqRing;
    }
    return ring_empty(ring->used_ring);
}


int releaseReqBuf(int bus, req_buf_ptr_t buf) {
    // sel4cp_dbg_puts("transport: releasing request buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }
    if (!buf) {
        return 0;
    }
    
    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2ReqRing;
    } else {
        ring = &m3ReqRing;
    }

    // Enqueue the buffer
    int ret = enqueue_free(ring, (uintptr_t)buf, I2C_BUF_SZ);
    if (ret != 0) {
        return 0;
    }
    return -1;
}

int releaseRetBuf(int bus, ret_buf_ptr_t buf) {
    // sel4cp_dbg_puts("transport: releasing return buffer\n");
    if (bus != 2 && bus != 3) {
        return 0;
    }
    if (!buf) {
        return 0;
    }
    
    // Allocate a buffer from the appropriate ring
    ring_handle_t *ring;
    if (bus == 2) {
        ring = &m2RetRing;
    } else {
        ring = &m3RetRing;
    }

    // Enqueue the buffer
    int ret = enqueue_free(ring, (uintptr_t)buf, I2C_BUF_SZ);
    if (ret != 0) {
        return 0;
    }
    return -1;
}