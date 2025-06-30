/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/config.h>
#include <sddf/i2c/devices/pn532/pn532.h>
#include <sddf/i2c/libi2c_raw.h>

// #define DEBUG_PN532

// NOTE: assumes no other I2C ops are running in same PD! If you need to use this interface
//       concurrently with another i2c peripheral in the same PD*, set PN532_SLICE_BASE such
//       that other devices won't compete for memory. This interface only needs 64 bytes of SLICE.
//
//       * (not recommended)
#ifndef PN532_SLICE_BASE
#define PN532_SLICE_BASE (0x0)
#endif

#ifndef I2C_SLICE_REGION
#define I2C_SLICE_REGION ((uint8_t *)i2c_config.slice.vaddr)
#endif

#ifdef DEBUG_PN532
#define LOG_PN532(...) do{ sddf_dprintf("PN532|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_PN532(...) do{}while(0)
#endif

// #define INCLUDE_ERROR_PN532

#ifdef INCLUDE_ERROR_PN532
#define LOG_PN532_ERR(...) do{ sddf_printf("PN532|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_PN532_ERR(...) do{}while(0)
#endif

/* These are defined in the client code. It is more convenient for these
   to be global variables than constantly pass them around. */
extern cothread_t t_event;
extern cothread_t t_main;

extern i2c_client_config_t i2c_config;
extern libi2c_conf_t libi2c_conf; // Client using the pn532 must initialise this variable using libi2c_init

extern i2c_queue_handle_t queue;
extern uintptr_t data_region;

#define ACK_FRAME_SIZE (7)

/*
* Read ACK frame has two parts, the first is to make the *request*
* to read the frame. Then we need to process the response to that
* request where we can actually check the data.
*/
uint8_t read_ack_frame(int retries)
{
    LOG_PN532("reading ack frame - %d retries\n", retries);
    uint8_t error = I2C_ERR_OK;
    int attempts = 0;
    uint8_t *slice_buf = (uint8_t *)(I2C_SLICE_REGION + PN532_SLICE_BASE);
    while (attempts < retries) {
        LOG_PN532("\t## %d \n", attempts);
        // Start: read FRAME_SIZE+1
        int ret = i2c_read(&libi2c_conf, PN532_I2C_BUS_ADDRESS, slice_buf, ACK_FRAME_SIZE + 1);
        if (ret != 0) {
            /*LOG_PN532_ERR("Failed to read ack frame! Retries = %d/%d\n", attempts, retries);*/
            attempts++;
            continue;
        }
        LOG_PN532("Got ACK frame response...\n");
        for (int i = 0; i < ACK_FRAME_SIZE + 1; i++) {
            LOG_PN532("\tslice_buf[%d] = 0x%x\n", i, slice_buf[i]);
        }
        const uint8_t PN532_ACK[] = { 0, 0, 0xFF, 0, 0xFF, 0 };

        if (slice_buf[0] & 1) { // to see if response is ready
            /* Minus one because the first byte is for the device ready status */
            int err = 1;
            for (int i = 0; i < ACK_FRAME_SIZE - 1; i++) {
                err = 0;
                if (slice_buf[i + 1] != PN532_ACK[i]) {
                    LOG_PN532_ERR("ACK malformed at index PN532_ACK[%d], value is %u, should be %u!\n", i,
                                  slice_buf[i + 1], PN532_ACK[i]);
                    error = I2C_ERR_OTHER;
                    attempts++;
                    err = 1;
                    break;
                }
            }
            if (err) {
                continue;
            }
            return I2C_ERR_OK;
        }
        /*LOG_PN532_ERR("Ack frame invalid! Retries = %d/%d\n", attempts, retries);*/
        attempts++;
        error = I2C_ERR_OTHER;
    }

    LOG_PN532_ERR("read_ack_frame: device is not ready yet!\n");

    return -1;
}

uint8_t pn532_write_command(uint8_t *header, uint8_t hlen, const uint8_t *body, uint8_t blen, int retries)
{
    LOG_PN532("writing command\n");
    uint8_t length = hlen + blen + 1;
    uint8_t *slice_buf = (uint8_t *)(I2C_SLICE_REGION + PN532_SLICE_BASE);
    uint16_t i2c_req_len = PN532_PREAMBLE_LEN + PN532_DATA_CHK_LEN + length + PN532_POSTAMBLE_LEN + 1;
    // Pack buffer
    slice_buf[0] = (PN532_PREAMBLE);
    slice_buf[1] = (PN532_STARTCODE1);
    slice_buf[2] = (PN532_STARTCODE2);

    /* Put length of PN532 data */
    slice_buf[3] = (length);

    /* Put checksum of length of PN532 data */
    slice_buf[4] = (~length + 1);
    LOG_PN532("Checksum (pream) = %x\n", (uint8_t)(~length + 1));
    slice_buf[5] = (PN532_HOSTTOPN532);

    uint8_t sum = PN532_HOSTTOPN532;
    for (int i = 0; i < hlen; i++) {
        sum += header[i];
        slice_buf[6 + i] = (header[i]);
    }

    for (int i = 0; i < blen; i++) {
        sum += body[i];
        slice_buf[6 + hlen + i] = (body[i]);
    }

    uint8_t checksum = (~sum) + 1;

    /* Postamble */
    slice_buf[6 + hlen + blen] = checksum;
    slice_buf[7 + hlen + blen] = (PN532_POSTAMBLE);

    int attempts, error = 0;
    error = i2c_write(&libi2c_conf, PN532_I2C_BUS_ADDRESS, slice_buf, i2c_req_len);
    if (!error) {
        LOG_PN532("Wrote command successfully. Reading ack frame\n");
        error = read_ack_frame(retries);
        if (error) {
            LOG_PN532("Error - read_ack_frame returned %d\n", error);
        }
        return error;
    }
    LOG_PN532_ERR("\twrite_command: failed!\n");
    attempts++;
    return error;
}

#define NACK_SIZE (6)

uint8_t read_response_length(int8_t *length, int retries)
{
    LOG_PN532("reading response length\n");
    size_t attempts = 0;
    uint8_t error = I2C_ERR_OK;
    uint8_t *slice_buf = (uint8_t *)(I2C_SLICE_REGION + PN532_SLICE_BASE);
    while (attempts < retries) {
        int error = i2c_read(&libi2c_conf, PN532_I2C_BUS_ADDRESS, slice_buf, NACK_SIZE + 1);
        if (error) {
            attempts++;
            continue;
        }

        if (!(slice_buf[0] & 1)) {
            LOG_PN532("device was not ready when reading the response length!\n");
            error = I2C_ERR_OTHER;
            attempts++;
        } else {
            break;
        }
    }

    if (attempts == retries) {
        LOG_PN532_ERR("\tread_response_length exhausted retries..\n");
        return error;
    }

    if (slice_buf[1] != PN532_PREAMBLE) {
        LOG_PN532_ERR("preamble incorrect!\n");
        return I2C_ERR_OTHER;
    }

    if (slice_buf[2] != PN532_STARTCODE1) {
        LOG_PN532_ERR("startcode1 incorrect!\n");
        return I2C_ERR_OTHER;
    }

    if (slice_buf[3] != PN532_STARTCODE2) {
        LOG_PN532_ERR("startcode2 incorrect!\n");
        return I2C_ERR_OTHER;
    }

    *length = slice_buf[4];

    LOG_PN532("checking nack for reading response length\n");

    /* Check nack */
    const uint8_t PN532_NACK[] = { 0, 0, 0xFF, 0xFF, 0, 0 };
    for (int i = 0; i < NACK_SIZE; i++) {
        slice_buf[i] = PN532_NACK[i];
    }
    error = i2c_write(&libi2c_conf, PN532_I2C_BUS_ADDRESS, slice_buf, NACK_SIZE);
    if (error) {
        LOG_PN532_ERR("read_response_len: failed to write NACK\n");
    }
    return error;
}

uint8_t pn532_read_response(uint8_t *buffer, uint8_t buffer_len, int retries)
{
    int8_t length;
    uint8_t *slice_buf = (uint8_t *)(I2C_SLICE_REGION + PN532_SLICE_BASE);
    uint8_t error = read_response_length(&length, retries);
    if (error != I2C_ERR_OK) {
        LOG_PN532_ERR("error trying to read response length\n");
        return error;
    } else if (length < 0) {
        LOG_PN532_ERR("read_response - length was less than zero\n");
        return I2C_ERR_OTHER;
    }

    LOG_PN532("reading response\n");
    LOG_PN532("length is : %d\n", length);

    size_t attempts = 0;
    while (attempts < retries) {
        size_t num_data_tokens = 6 + length + 2;
        if (num_data_tokens > i2c_config.slice.size) {
            LOG_PN532_ERR("Request size overflows slice region!\n");
            return I2C_ERR_OTHER;
        }

        LOG_PN532("read_response: sent request of size %z\n", num_data_tokens);
        int error = i2c_read(&libi2c_conf, PN532_I2C_BUS_ADDRESS, slice_buf, num_data_tokens);
        if (error) {
            attempts++;
            continue;
        }

        if (!(slice_buf[0] & 1)) {
            LOG_PN532("not ready yet\n");
            for (int i = 0; i < num_data_tokens; i++) {
                LOG_PN532("\tslice_buf[%d] = 0x%x\n", i, slice_buf[i]);
            }
            error = I2C_ERR_OTHER;
            attempts++;
            continue;
        } else {
            break;
        }
    }

    if (attempts >= retries) {
        LOG_PN532_ERR("\tread_response exhausted retries..\n");
        return -1;
    }

    // Read PREAMBLE
    if (slice_buf[1] != PN532_PREAMBLE) {
        LOG_PN532_ERR("read_response: PREAMBLE check failed\n");
        return I2C_ERR_OTHER;
    }
    // Read STARTCODE1
    if (slice_buf[2] != PN532_STARTCODE1) {
        LOG_PN532_ERR("read_response: STARTCODE1 check failed\n");
        return I2C_ERR_OTHER;
    }
    // Read STARTCODE2
    if (slice_buf[3] != PN532_STARTCODE2) {
        LOG_PN532_ERR("read_response: STARTCODE2 check failed\n");
        return I2C_ERR_OTHER;
    }
    // Read length
    uint8_t data_length = slice_buf[4];
    if (data_length != length) {
        LOG_PN532_ERR("Received data_length of 0x%ux, was expecting 0x%x\n", data_length, length);
        return I2C_ERR_OTHER;
    }

    // Read command data
    if (data_length > buffer_len) {
        LOG_PN532_ERR("returned data length (0x%ux) greater than user-provided buffer length (0x%x)\n", data_length,
                      buffer_len);
        return I2C_ERR_OTHER;
    }

    for (int i = 0; i < data_length; i++) {
        buffer[i] = slice_buf[8 + i];
    }
    return I2C_ERR_OK;
}
