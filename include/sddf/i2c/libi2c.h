/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// I2C interface library for clients using libmicrokitco.
// Provides helper functions for creating requests and handing them to the virtualiser.
//
// Currently this interface only supports single command requests, but the protocol is capable
// of doing many command requests. This is simply because multi-command requests are not
// necessary in most cases! If your usage requires more commands per request, do not use
// this library and instead implement direct calls to the protocol in <sddf/i2c/queue.h>
//
// See i2c/queue.h for details about the I2C transport layer.

#pragma once
#include <stdint.h>
#include <sddf/i2c/queue.h>
#include <sddf/util/printf.h>
#include <sddf/i2c/config.h>
#ifdef LIBI2C_RAW
#include <libco.h>
// Client must define and set up these cothreads for this interface to function.
extern cothread_t t_event;
extern cothread_t t_main;
#else
#include <libmicrokitco.h>
#endif

// Client must define this. E.g.
// __attribute__((__section__(".i2c_client_config"))) i2c_client_config_t i2c_config;
extern i2c_client_config_t i2c_config;

#define I2C_DATA_REGION ((uint8_t *)i2c_config.data.vaddr)

#define LOG_LIBI2C_ERR(...) do{ sddf_printf("LIBI2C|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/*
 * The sDDF I2C protocol reduces all I2C transactions into a series of commands.
 * Commands may designate any of the following operations:
 * 1. A read of N bytes, stored in buffer B.
 * 2. A read of N bytes from device register R, with register address R stored in the first byte of the read buffer B. Overwritten with read data on return.
 * 3. A write of N bytes, supplied by buffer B. Writes to device registers are expressed by
 *    putting the register address in the first byte of the write buffer.
 *
 *  Any of these command types may optionally use the following flags:
 *  * RSTART: repeated start
 *  Other flags are used to describe a read, write or write-read (sub-address read)
 */

typedef struct libi2c_conf {
    i2c_queue_handle_t *handle;
    i2c_cmd_t *data_start;   // Pointer to first command in data region
} libi2c_conf_t;

int libi2c_init(libi2c_conf_t *conf_struct, i2c_queue_handle_t *queue_handle);
static i2c_cmd_t *__libi2c_alloc_cmd(libi2c_conf_t *conf);
int sddf_i2c_write(libi2c_conf_t *conf, i2c_addr_t address, void *write_buf, uint16_t len);
int sddf_i2c_read(libi2c_conf_t *conf, i2c_addr_t address, void *read_buf, uint16_t len);
int sddf_i2c_writeread(libi2c_conf_t *conf, i2c_addr_t address, i2c_addr_t reg_address, void *read_buf, uint16_t len);
int i2c_dispatch(libi2c_conf_t *conf, i2c_addr_t address, void *buf, uint16_t len, uint8_t flag_mask);
