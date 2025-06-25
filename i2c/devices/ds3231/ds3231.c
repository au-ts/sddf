/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Stateless driver interface for the Analogue Devices DS3231 I2C real-time clock.
// Used with a client, such as client-ds3231 in /examples/i2c
// NOTE: assumes no other I2C ops are running in same PD! If you need to use this interface
//       concurrently with another i2c peripheral, set DS3231_COMMAND_BASE such that other devices
//       won't compete for memory. This interface only needs 16 bytes of COMMAND.

#include <stdint.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <sddf/i2c/config.h>
#include <sddf/i2c/devices/ds3231/ds3231.h>
#include <sddf/i2c/libi2c_raw.h>

// #define DEBUG_DS3231

#ifndef DS3231_COMMAND_BASE
#define DS3231_COMMAND_BASE (0x0)
#endif

#ifdef DEBUG_DS3231
#define LOG_DS3231(...) do{ sddf_dprintf("DS3231|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DS3231(...) do{}while(0)
#endif

#define LOG_DS3231_ERR(...) do{ sddf_printf("DS3231|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

bool delay_ms(size_t milliseconds);

extern cothread_t t_event;
extern cothread_t t_main;
// Extern definitions of structs owned by the client that uses this driver interface
extern libi2c_conf_t libi2c_conf; // Client using the ds3231 must initialise this variable using libi2c_init
extern i2c_client_config_t i2c_config;

#ifndef I2C_COMMAND_REGION
#define I2C_COMMAND_REGION ((uint8_t *)i2c_config.command.vaddr)
#endif

/**
 *  Write the contents of slice to the DS3231. Buffer not assumed to be in COMMAND region due to
 *  legacy, copied into slice_region instead.
 */
int ds3231_write(uint8_t *slice, uint16_t slice_len, size_t retries)
{
    // Only read or write ever occurs at one time for this device
    size_t attempts = 1;
    while (true) {
        if (attempts == retries)
            return -1;
        uint8_t *slice_region_buf = (uint8_t *)(I2C_COMMAND_REGION + DS3231_COMMAND_BASE);

        // Copy to slice_region region
        for (int i = 0; i < slice_len; i++) {
            slice_region_buf[i] = slice[i];
        }

        int error = i2c_write(&libi2c_conf, DS3231_I2C_BUS_ADDRESS, slice_region_buf, slice_len);
        if (!error) {
            return error;
        }

        attempts++;
        delay_ms(1);
    }
}
/**
  * Read from the DS3231 and store data in *slice_region_slice. Must be allocated from
  * the COMMAND shared memory region mapped into the client.
  */
int ds3231_read(uint8_t *slice_region_slice, i2c_addr_t reg_addr, uint16_t slice_len, size_t retries)
{
    size_t attempts = 1;
    while (true) {
        if (attempts == retries)
            return -1;
        // Set register address
        int error = i2c_writeread(&libi2c_conf, DS3231_I2C_BUS_ADDRESS, reg_addr, (uint8_t *)(slice_region_slice),
                                  slice_len);
        if (!error) {
            return error;
        }
        attempts++;
        delay_ms(1);
    }
}

int ds3231_get_time(uint8_t *second, uint8_t *minute, uint8_t *hour, uint8_t *day_of_week, uint8_t *day, uint8_t *month,
                    uint8_t *year)
{
    uint8_t *slice_region_buf = (uint8_t *)(I2C_COMMAND_REGION + DS3231_COMMAND_BASE);

    uint8_t read_fail = ds3231_read(slice_region_buf, DS3231_REGISTER_SECONDS, 7, DEFAULT_READ_RESPONSE_RETRIES);
    if (read_fail) {
        return -1;
    }

    *second = bcd_to_dec(slice_region_buf[0]);
    *minute = bcd_to_dec(slice_region_buf[1]);
    *hour = bcd_to_dec(slice_region_buf[2]);
    *day_of_week = bcd_to_dec(slice_region_buf[3]);
    *day = bcd_to_dec(slice_region_buf[4]);
    *month = bcd_to_dec(slice_region_buf[5] & (~(1 << DS3231_BIT_CENTURY))); // mask out the century
    *year = bcd_to_dec(slice_region_buf[6]);

    return 0;
}

int ds3231_set_time(uint8_t second, uint8_t minute, uint8_t hour, uint8_t day_of_week, uint8_t day, uint8_t month,
                    uint8_t year)
{
    uint8_t set_time_slice[8];
    set_time_slice[0] = DS3231_REGISTER_SECONDS; // Address to start writing at
    set_time_slice[1] = dec_to_bcd(second);
    set_time_slice[2] = dec_to_bcd(minute);
    set_time_slice[3] = dec_to_bcd(hour);
    set_time_slice[4] = dec_to_bcd(day_of_week);
    set_time_slice[5] = dec_to_bcd(day);
    set_time_slice[6] = dec_to_bcd(month);
    set_time_slice[7] = dec_to_bcd(year);

    uint8_t write_fail = ds3231_write(set_time_slice, 8, DEFAULT_READ_ACK_FRAME_RETRIES);
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
