/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/devices/pn532/pn532.h>
#include "client.h"

//#define DEBUG_PN532

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

extern cothread_t t_event;
extern cothread_t t_main;

struct request {
    uint8_t *buffer;
    /* Maximum amount of data the buffer can hold */
    size_t buffer_size;
    /* How many I2C tokens for processing we have enqueued */
    size_t data_offset_len;
    /* Bus address we are sending to */
    size_t bus_address;
};

struct response {
    /* Client-side address for buffer to be used as response */
    uint8_t *buffer;
    size_t data_size;
    size_t read_idx;
};

/* These are defined in the client code. It is more convenient for these
   to be global variables than constantly pass them around. */
extern i2c_queue_handle_t queue;
extern uintptr_t data_region;

/* Below is a simple API for quickly making requests and sending them off as well
 * as reading from the responses.
 * It should be noted that this code has a big assumption right now which is fine
 * for this system but perhaps not all systems that would make use of I2C.
 * The assumption is that we only have one request at a time until we get a response.
 * This assumption lets us use the same region of memory within the data region for
 * all of our requests and responses, as since it is one-by-one it will never be
 * over-written.
 */

void response_init(struct response *response)
{
    uintptr_t offset = 0;
    unsigned int buffer_len = 0;
    /* This is unused as for our PN532 client only talks to a single I2C bus address. */
    size_t bus_address = 0;
    int ret = i2c_dequeue_response(queue, &bus_address, &offset, &buffer_len);
    if (ret) {
        LOG_PN532_ERR("response_init could not dequeue used response buffer!\n");
        return;
    }

    response->buffer = (uint8_t *) data_region + offset;
    response->data_size = buffer_len;
    response->read_idx = 0;
}

uint8_t response_read(struct response *response)
{
    if (response->read_idx >= response->data_size) {
        LOG_PN532_ERR("trying to read more data than exists in response (buffer: %p)\n", response->buffer);
        return 0;
    }

    uint8_t value = response->buffer[RESPONSE_DATA_OFFSET + response->read_idx];
    response->read_idx++;

    return value;
}

void response_finish(struct response *response)
{
    // Do nothing
}

void request_init(struct request *req, uint8_t bus_address)
{
    req->data_offset_len = 0;
    req->buffer = (uint8_t *)data_region;
    req->buffer_size = I2C_MAX_DATA_SIZE;
    req->bus_address = bus_address;
}

void request_add(struct request *req, uint8_t data)
{
    size_t index = req->data_offset_len;
    if (index >= req->buffer_size) {
        LOG_PN532_ERR("request buffer is full (size is 0x%lx)\n", req->buffer_size);
        return;
    }
    req->buffer[index] = data;
    req->data_offset_len++;
}

void request_send(struct request *req)
{
    int err = i2c_enqueue_request(queue, req->bus_address, (size_t) req->buffer - data_region, req->data_offset_len);
    if (err) {
        LOG_PN532_ERR("failed to enqueue request buffer!\n");
    }

    microkit_notify(I2C_VIRTUALISER_CH);
}

static uint8_t process_return_buffer(struct response *response)
{
    LOG_PN532("processing return buffer\n");

    if (RESPONSE_ERR >= response->data_size) {
        LOG_PN532_ERR("trying to read more data than exists in response (buffer: %p).\n", response->buffer);
        return I2C_ERR_OTHER;
    }

    uint8_t error = response->buffer[RESPONSE_ERR];

    if (error) {
        LOG_PN532_ERR("Previous request failed where RESPONSE_ERR is 0x%lx\n", error);
    }

    return error;
}

#define ACK_FRAME_SIZE (7)

/*
* Read ACK frame has two parts, the first is to make the *request*
* to read the frame. Then we need to process the response to that
* request where we can actually check the data.
*/
uint8_t read_ack_frame(size_t retries)
{
    LOG_PN532("reading ack frame\n");
    uint8_t error;
    size_t attempts = 0;
    while (attempts < retries) {
        struct request req = {};
        request_init(&req, PN532_I2C_BUS_ADDRESS);

        request_add(&req, I2C_TOKEN_START);
        request_add(&req, I2C_TOKEN_ADDR_READ);
        request_add(&req, ACK_FRAME_SIZE + 1);      // Add request data size
        for (int i = 0; i <= ACK_FRAME_SIZE; i++) {
            request_add(&req, 0x0); /* Temporary - logic to skip this step will be added as
                                       part of issue 211 https://github.com/au-ts/sddf/issues/211 */
        }
        request_add(&req, I2C_TOKEN_STOP);

        request_send(&req);

        co_switch(t_event);
        assert(i2c_queue_length(queue.response) == 1);

        const uint8_t PN532_ACK[] = {0, 0, 0xFF, 0, 0xFF, 0};

        struct response response = {};

        response_init(&response);

        uint8_t error = process_return_buffer(&response);
        if (error) {
            LOG_PN532_ERR("return buffer error");
            response_finish(&response);
            attempts++;
            continue;
        }

        if (response_read(&response) & 1) { // to see if response is ready
            /* Minus one because the first byte is for the device ready status */
            for (int i = 0; i < ACK_FRAME_SIZE - 1; i++) {
                uint8_t value = response_read(&response);
                if (value != PN532_ACK[i]) {
                    LOG_PN532_ERR("ACK malformed at index PN532_ACK[%d], value is %d!\n", i, value);
                    response_finish(&response);
                    error = I2C_ERR_OTHER;
                    attempts++;
                    continue;
                }
            }

            response_finish(&response);
            return I2C_ERR_OK;
        }
        attempts++;
        error = I2C_ERR_OTHER;
        response_finish(&response);
    }

    LOG_PN532_ERR("read_ack_frame: device is not ready yet!\n");
    return error;
}

uint8_t pn532_write_command(uint8_t *header, uint8_t hlen, const uint8_t *body, uint8_t blen, size_t retries)
{
    LOG_PN532("writing command\n");
    struct request req = {};
    size_t length = hlen + blen + 1;
    request_init(&req, PN532_I2C_BUS_ADDRESS);

    request_add(&req, I2C_TOKEN_START);
    request_add(&req, I2C_TOKEN_ADDR_WRITE);
    // Write length of write transaction preamble + data length + checksum bytes
    request_add(&req, PN532_PREAMBLE_LEN + PN532_DATA_CHK_LEN + length + PN532_POSTAMBLE_LEN);

    request_add(&req, PN532_PREAMBLE);
    request_add(&req, PN532_STARTCODE1);
    request_add(&req, PN532_STARTCODE2);

    /* Put length of PN532 data */
    request_add(&req, length);

    /* Put checksum of length of PN532 data */
    request_add(&req, ~length + 1);
    request_add(&req, PN532_HOSTTOPN532);

    uint8_t sum = PN532_HOSTTOPN532;
    for (int i = 0; i < hlen; i++) {
        sum += header[i];
        request_add(&req, header[i]);
    }

    for (int i = 0; i < blen; i++) {
        sum += body[i];
        request_add(&req, body[i]);
    }

    uint8_t checksum = ~sum + 1;
    request_add(&req, checksum);

    request_add(&req, PN532_POSTAMBLE);

    request_add(&req, I2C_TOKEN_STOP);

    request_send(&req);

    /* Now we need to wait for the response */
    co_switch(t_event);
    assert(i2c_queue_length(queue.response) == 1);

    struct response response = {};
    response_init(&response);

    uint8_t error = process_return_buffer(&response);

    response_finish(&response);

    if (!error) {
        error = read_ack_frame(retries);
        return error;
    }
    return error;
}

#define NACK_SIZE (6)

uint8_t read_response_length(int8_t *length, size_t retries)
{
    LOG_PN532("reading response length\n");

    struct response response = {};

    size_t attempts = 0;
    uint8_t error = I2C_ERR_OK;
    while (attempts < retries) {
        struct request req = {};
        request_init(&req, PN532_I2C_BUS_ADDRESS);

        request_add(&req, I2C_TOKEN_START);
        request_add(&req, I2C_TOKEN_ADDR_READ);
        request_add(&req, NACK_SIZE + 1);       // Add request size

        for (int i = 0; i <= NACK_SIZE; i++) {
            request_add(&req, 0x0);             // Temporary - logic to skip this step will be added as
        }                                       // part of issue 211 https://github.com/au-ts/sddf/issues/211
        request_add(&req, I2C_TOKEN_STOP);

        request_send(&req);

        co_switch(t_event);
        assert(i2c_queue_length(queue.response) == 1);

        response_init(&response);

        uint8_t error = process_return_buffer(&response);
        if (error) {
            response_finish(&response);
            attempts++;
            continue;
        }

        if (!(response_read(&response) & 1)) {
            LOG_PN532_ERR("device was not ready when reading the response length!\n");
            response_finish(&response);
            error = I2C_ERR_OTHER;
            attempts++;
        } else {
            break;
        }
    }

    if (attempts == retries) {
        return error;
    }

    if (response_read(&response) != PN532_PREAMBLE) {
        LOG_PN532_ERR("preamble incorrect!\n");
        response_finish(&response);
        return I2C_ERR_OTHER;
    }

    if (response_read(&response) != PN532_STARTCODE1) {
        LOG_PN532_ERR("startcode1 incorrect!\n");
        response_finish(&response);
        return I2C_ERR_OTHER;
    }

    if (response_read(&response) != PN532_STARTCODE2) {
        LOG_PN532_ERR("startcode2 incorrect!\n");
        response_finish(&response);
        return I2C_ERR_OTHER;
    }

    *length = response_read(&response);
    response_finish(&response);

    LOG_PN532("checking nack for reading response length\n");

    /* Check nack */
    const uint8_t PN532_NACK[] = {0, 0, 0xFF, 0xFF, 0, 0};
    struct request nack_req = {};
    request_init(&nack_req, PN532_I2C_BUS_ADDRESS);

    request_add(&nack_req, I2C_TOKEN_START);
    request_add(&nack_req, I2C_TOKEN_ADDR_WRITE);
    request_add(&nack_req, NACK_SIZE);          // Add write size
    for (int i = 0; i < NACK_SIZE; i++) {
        request_add(&nack_req, PN532_NACK[i]);
    }
    request_add(&nack_req, I2C_TOKEN_STOP);
    request_send(&nack_req);

    co_switch(t_event);
    assert(i2c_queue_length(queue.response) == 1);

    struct response response2 = {};
    response_init(&response2);

    error = process_return_buffer(&response2);

    response_finish(&response2);

    return error;
}

uint8_t pn532_read_response(uint8_t *buffer, uint8_t buffer_len, size_t retries)
{
    int8_t length;
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

    struct response response = {};

    size_t attempts = 0;
    while (attempts < retries) {
        struct request request = {};
        request_init(&request, PN532_I2C_BUS_ADDRESS);

        size_t num_data_tokens = 6 + length + 2;

        request_add(&request, I2C_TOKEN_START);
        request_add(&request, I2C_TOKEN_ADDR_READ);
        request_add(&request, num_data_tokens);     // Add number of bytes to read

        if (num_data_tokens > request.buffer_size) {
            LOG_PN532_ERR("number of request data tokens (0x%lx) exceeds buffer size (0x%lx)\n", num_data_tokens,
                          request.buffer_size);
            return I2C_ERR_OTHER;
        }

        for (int i = 0; i < num_data_tokens; i++) {
            request_add(&request, 0x0);     // Temporary - logic to skip this step will be added as
        }                                   // part of issue 211 https://github.com/au-ts/sddf/issues/211

        request_add(&request, I2C_TOKEN_STOP);

        request_send(&request);

        LOG_PN532("read_response: sent request of size %d\n", num_data_tokens);
        co_switch(t_event);
        assert(i2c_queue_length(queue.response) == 1);

        response_init(&response);
        error = process_return_buffer(&response);
        if (error) {
            response_finish(&response);
            attempts++;
            continue;
        }

        if (!(response_read(&response) & 1)) {
            response_finish(&response);
            LOG_PN532_ERR("not ready yet\n");
            error = I2C_ERR_OTHER;
            attempts++;
            continue;
        } else {
            break;
        }
    }

    // Read PREAMBLE
    if (response_read(&response) != PN532_PREAMBLE) {
        LOG_PN532_ERR("read_response: PREAMBLE check failed\n");
        response_finish(&response);
        return I2C_ERR_OTHER;
    }
    // Read STARTCODE1
    if (response_read(&response) != PN532_STARTCODE1) {
        LOG_PN532_ERR("read_response: STARTCODE1 check failed\n");
        response_finish(&response);
        return I2C_ERR_OTHER;
    }
    // Read STARTCODE2
    if (response_read(&response) != PN532_STARTCODE2) {
        LOG_PN532_ERR("read_response: STARTCODE2 check failed\n");
        response_finish(&response);
        return I2C_ERR_OTHER;
    }
    // Read length
    size_t data_length = response_read(&response);
    if (data_length != length) {
        LOG_PN532_ERR("Received data_length of 0x%lx, was expecting 0x%x\n", data_length, length);
        response_finish(&response);
        return I2C_ERR_OTHER;
    }

    // Read checksum of length
    response_read(&response);

    // Read response command
    response_read(&response);

    response_read(&response);
    // Read command data
    if (data_length > buffer_len) {
        LOG_PN532_ERR("returned data length (0x%lx) greater than user-provided buffer length (0x%x)\n", data_length,
                      buffer_len);
        response_finish(&response);
        return I2C_ERR_OTHER;
    }

    for (int i = 0; i < data_length; i++) {
        buffer[i] = response_read(&response);
    }

    // Read checksum of data
    response_read(&response);

    // Read postamble
    response_read(&response);

    response_finish(&response);

    return I2C_ERR_OK;
}
