/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// i2c-transport.h
// Header for sDDF i2c transport layer. Each instance of this module
// is split into a Control and Client half. The Control is always the i2c
// server while the Client is either an i2c driver or a client of the i2c.
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 08/2023

#ifndef I2C_TRANSPORT_H
#define I2C_TRANSPORT_H
#include <stdint.h>
#include <stddef.h>
#include <sw_shared_ringbuffer.h>
#include <string.h>
#include "i2c-token.h"


// Return buffer
#define RET_BUF_ERR 0
#define RET_BUF_ERR_TK 1
#define RET_BUF_CLIENT 2
#define RET_BUF_ADDR 3
#define RET_BUF_DAT_OFFSET 4    // Number of non-payload bytes. Should match however
                                // many #defines are listed here.

// Request buffer
#define REQ_BUF_CLIENT 0
#define REQ_BUF_ADDR 1
#define REQ_BUF_DAT_OFFSET 2    // Number of non-payload bytes. Should match however
                                // many #defines are listed here.

// Shared memory regions
extern uintptr_t req_free;
extern uintptr_t req_used;
extern uintptr_t ret_free;
extern uintptr_t ret_used;
extern uintptr_t driver_bufs;

extern ring_handle_t reqRing;
extern ring_handle_t retRing;



// Metadata is encoded differently in returns vs. requests so we
// have two types for "safety" provided by the compiler. It sometimes
// bothers to give warnings for this.
typedef volatile uint8_t *ret_buf_ptr_t;
typedef volatile uint8_t *req_buf_ptr_t;

/**
 * Initialise the transport layer. Sets up shared ring buffers
 * and their associated transport buffers.
 */
void i2cTransportInit(int buffer_init);

/**
 * Allocate a request buffer to push data into the driver for a specified
 * i2c master interface (bus). This function loads the data into the buffer.
 * Buffers are allocated from the free pool and loaded with data into the used pool.
 * 
 * The first two bytes of the buffer store the client ID and address respectively
 * to be used for bookkeeping.
 * 
 * @note Expects that data is properly formatted with END token terminator.
 * 
 * @param size: Size of the data to be loaded into the buffer. Max I2C_BUF_SZ
 * @param data: Pointer to the data to be loaded into the buffer
 * @param client: Protection domain of the client who requested this.
 * @param addr: 7-bit I2C address to be used for the transaction
 * @return Pointer to the buffer allocated for this request
*/
req_buf_ptr_t allocReqBuf(size_t size, uint8_t *data, uint8_t client, uint8_t addr);

/**
 * Release a request buffer to the free pool.
*/
int releaseReqBuf(req_buf_ptr_t buf);

/**
 * Allocate a return buffer to get data back to the server from the driver, given a
 * i2c master interface (bus). The buffer is just allocated and does not get moved
 * into the used queue by this function, unlike `allocReqBuf`.
 * Address and client are used to demultiplex by the server.
 * 
 * Buffers are allocated from the free pool, but are not put into the used pool.
 * 
 * @note Expects that data is properly formatted with END token terminator.
 * 
 * @param bus: EE domain i2c master interface number

 * @return Pointer to the buffer allocated for this request
*/
ret_buf_ptr_t getRetBuf(void);


/**
 * Release a return buffer to the free pool.
*/
int releaseRetBuf(ret_buf_ptr_t buf);

/**
 * Push a return buffer back to the server for a specified i2c master interface (bus).
 * This should only operate on the buffers given by `allocRetBuf`. Puts buffers into
 * the used queue.
 * 
 * @param bus: EE domain i2c master interface number
 * @param buf: Pointer to the buffer to be pushed back to the server
 * @param sz: Size of the buffer to be pushed back to the server
 * @return 0 on success
*/
int pushRetBuf(ret_buf_ptr_t buf, size_t size);

/**
 * Pop a return buffer from the server for a specified i2c master interface (bus).
 * Removes buffer from the used pool but does not put it in the free queue.
 * @return Pointer to buffer containing request from the server.
*/
req_buf_ptr_t popReqBuf(size_t *size);


/**
 * Pop a return buffer from the driver to be returned to the clients.
 * Removes buffer from the used pool but does not put it in the free queue.
 * @return Pointer to buffer containing data from the driver.
*/
ret_buf_ptr_t popRetBuf(size_t *size);

int retBufEmpty(void);
int reqBufEmpty(void);


// Errors
#define I2C_ERR_OK 0
#define I2C_ERR_TIMEOUT 1
#define I2C_ERR_NACK 2
#define I2C_ERR_NOREAD 3
#endif