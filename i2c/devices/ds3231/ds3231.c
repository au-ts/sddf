/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <client.h>
#include <sddf/i2c/devices/ds3231/ds3231.h>

// #define DEBUG_DS3231

#ifdef DEBUG_DS3231
#define LOG_DS3231(...) do{ sddf_dprintf("DS3231|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DS3231(...) do{}while(0)
#endif

#define LOG_DS3231_ERR(...) do{ sddf_printf("DS3231|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


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
    size_t bus_address = 0;
    int ret = i2c_dequeue_response(queue, &bus_address, &offset, &buffer_len);
    if (ret) {
        LOG_DS3231_ERR("response_init could not dequeue used response buffer!\n");
        return;
    }

    response->buffer = (uint8_t *) data_region + offset;
    response->data_size = buffer_len;
    response->read_idx = 0;
}

uint8_t response_read(struct response *response)
{
    if (response->read_idx >= response->data_size) {
        LOG_DS3231_ERR("trying to read more data than exists in response (buffer: %p)\n", response->buffer);
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
        LOG_DS3231_ERR("request buffer is full (size is 0x%lx)\n", req->buffer_size);
        return;
    }
    req->buffer[index] = data;
    req->data_offset_len++;
}

void request_send(struct request *req)
{
    int err = i2c_enqueue_request(queue, req->bus_address, (size_t) req->buffer - data_region, req->data_offset_len);
    if (err) {
        LOG_DS3231_ERR("failed to enqueue request buffer!\n");
    }

    microkit_notify(I2C_VIRTUALISER_CH);
}

static uint8_t process_return_buffer(struct response *response)
{
    LOG_DS3231("processing return buffer\n");

    if (RESPONSE_ERR >= response->data_size) {
        LOG_DS3231_ERR("trying to read more data than exists in response (buffer: %p).\n", response->buffer);
        return I2C_ERR_OTHER;
    }

    uint8_t error = response->buffer[RESPONSE_ERR];

    if (error) {
        LOG_DS3231_ERR("Previous request failed where RESPONSE_ERR is 0x%x\n", error);
    }

    return error;
}

bool ds3231_write(uint8_t *buffer, uint8_t buffer_len, size_t retries)
{
    size_t attempts = 1;
    while (true) {
        struct request req = {};
        request_init(&req, DS3231_I2C_BUS_ADDRESS);
        request_add(&req, I2C_TOKEN_START);
        request_add(&req, I2C_TOKEN_ADDR_WRITE);
        request_add(&req, buffer_len); // Add buffer size

        for (int i = 0; i < buffer_len; i++) {
            request_add(&req, buffer[i]);
        }

        request_add(&req, I2C_TOKEN_STOP);
        request_add(&req, I2C_TOKEN_END);

        request_send(&req);

        co_switch(t_event);

        struct response response = {};
        response_init(&response);

        uint8_t error = process_return_buffer(&response);

        response_finish(&response);

        if (!error || attempts == retries) {
            return error;
        }

        attempts++;
        delay_ms(1);
    }
}

bool ds3231_read(uint8_t *buffer, uint8_t buffer_len, size_t retries)
{
    size_t attempts = 1;
    while (true) {
        struct request req = {};
        request_init(&req, DS3231_I2C_BUS_ADDRESS);

        request_add(&req, I2C_TOKEN_START);
        request_add(&req, I2C_TOKEN_ADDR_READ);
        request_add(&req, buffer_len);      // Add read length

        for (int i = 0; i < buffer_len - 1; i++) {
            request_add(&req, 0x0);             // Temporary - will be changed as part of
        }                                       // issue 211 https://github.com/au-ts/sddf/issues/211

        request_add(&req, I2C_TOKEN_STOP);

        request_send(&req);

        co_switch(t_event);

        struct response response = {};
        response_init(&response);
        uint8_t error = process_return_buffer(&response);
        if (!error) {
            for (int i = 0; i < buffer_len; i++) {
                buffer[i] = response_read(&response);
            }

            response_finish(&response);
            return error;

        } else if (attempts == retries) {
            return error;
        }
        attempts++;
        delay_ms(1);
    }
}

bool ds3231_get_time(uint8_t *second, uint8_t *minute, uint8_t *hour, uint8_t *day_of_week, uint8_t *day,
                     uint8_t *month, uint8_t *year)
{
    uint8_t start_register_write_buffer[1];
    start_register_write_buffer[0] = DS3231_REGISTER_SECONDS; // to tell ds3231 to start reading at register 0
    uint8_t write_fail = ds3231_write(start_register_write_buffer, 1, DEFAULT_READ_ACK_FRAME_RETRIES);
    if (write_fail) {
        return true;
    }

    uint8_t time_response_buffer[7];
    uint8_t read_fail = ds3231_read(time_response_buffer, 7, DEFAULT_READ_RESPONSE_RETRIES);
    if (read_fail) {
        return true;
    }

    *second = bcd_to_dec(time_response_buffer[0]);
    *minute = bcd_to_dec(time_response_buffer[1]);
    *hour = bcd_to_dec(time_response_buffer[2]);
    *day_of_week = bcd_to_dec(time_response_buffer[3]);
    *day = bcd_to_dec(time_response_buffer[4]);
    *month = bcd_to_dec(time_response_buffer[5] & (~(1 << DS3231_BIT_CENTURY))); // mask out the century
    *year = bcd_to_dec(time_response_buffer[6]);

    return false;
}

bool ds3231_set_time(uint8_t second, uint8_t minute, uint8_t hour, uint8_t day_of_week, uint8_t day, uint8_t month,
                     uint8_t year)
{
    uint8_t set_time_buffer[8];
    set_time_buffer[0] = DS3231_REGISTER_SECONDS; // Address to start writing at
    set_time_buffer[1] = dec_to_bcd(second);
    set_time_buffer[2] = dec_to_bcd(minute);
    set_time_buffer[3] = dec_to_bcd(hour);
    set_time_buffer[4] = dec_to_bcd(day_of_week);
    set_time_buffer[5] = dec_to_bcd(day);
    set_time_buffer[6] = dec_to_bcd(month);
    set_time_buffer[7] = dec_to_bcd(year);

    uint8_t write_fail = ds3231_write(set_time_buffer, 8, DEFAULT_READ_ACK_FRAME_RETRIES);
    return write_fail;
}

// Function to convert decimal to BCD
uint8_t dec_to_bcd(uint8_t val)
{
    return ((val / 10 * 16) + (val % 10));
}

// Function to convert BCD to decimal
uint8_t bcd_to_dec(uint8_t val)
{
    return ((val / 16 * 10) + (val % 16));
}
