/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define DS3231_I2C_BUS_ADDRESS (0x68)

enum ds3231_registers {                         // RANGE:
    DS3231_REGISTER_SECONDS,                    // 00–59
    DS3231_REGISTER_MINUTES,                    // 00–59
    DS3231_REGISTER_HOURS,                      // 1–12 + AM/PM 10 Hour 00–23
    DS3231_REGISTER_DAY_OF_WEEK,                // 1–7
    DS3231_REGISTER_DATE,                       // 00–31
    DS3231_REGISTER_MONTH,                      // 01–12 + Century
    DS3231_REGISTER_YEAR,                       // 00–99
    DS3231_REGISTER_ALARM1_SECONDS,
    DS3231_REGISTER_ALARM1_MINUTES,
    DS3231_REGISTER_ALARM1_HOURS,
    DS3231_REGISTER_ALARM1_DAY_OF_WEEK_OR_DATE,
    DS3231_REGISTER_ALARM2_MINUTES,
    DS3231_REGISTER_ALARM2_HOURS,
    DS3231_REGISTER_ALARM2_DAY_OF_WEEK_OR_DATE,
    DS3231_REGISTER_CONTROL,
    DS3231_REGISTER_CONTROL_STATUS,
    DS3231_REGISTER_AGING_OFFSET,
    DS3231_REGISTER_ALARM2_TEMP_MSB,
    DS3231_REGISTER_ALARM2_TEMP_LSB
};
// Below are the bit numbers of the respective field
#define DS3231_BIT_12_24                      0X06
#define DS3231_BIT_CENTURY                    0X07
#define DS3231_BIT_A1M1                       0X07
#define DS3231_BIT_A1M2                       0X07
#define DS3231_BIT_A1M3                       0X07
#define DS3231_BIT_A1M4                       0X07
#define DS3231_BIT_A2M2                       0X07
#define DS3231_BIT_A3M3                       0X07
#define DS3231_BIT_A4M4                       0X07
#define DS3231_BIT_12_24_ALARM1               0X06
#define DS3231_BIT_12_24_ALARM2               0X06
#define DS3231_BIT_DY_DT_ALARM1               0X06
#define DS3231_BIT_DY_DT_ALARM2               0X06
#define DS3231_BIT_A1IE                       0X00
#define DS3231_BIT_A2IE                       0X01
#define DS3231_BIT_INTCN                      0X02
#define DS3231_BIT_RS1                        0X03
#define DS3231_BIT_RS2                        0X04
#define DS3231_BIT_CONV                       0X05
#define DS3231_BIT_BBSQW                      0X06
#define DS3231_BIT_EOSC                       0X07
#define DS3231_BIT_A1F                        0X00
#define DS3231_BIT_A2F                        0X01
#define DS3231_BIT_BSY                        0X02
#define DS3231_BIT_EN32KHZ                    0X03
#define DS3231_BIT_OSF                        0X07

#define DEFAULT_READ_RESPONSE_RETRIES (256)
#define DEFAULT_READ_ACK_FRAME_RETRIES (20)

bool ds3231_write(uint8_t *buffer, uint8_t buffer_len, size_t retries);
bool ds3231_read(uint8_t *buffer, uint8_t buffer_len, size_t retries);

// User Provided Functions
bool ds3231_get_time(uint8_t *seconds, uint8_t *minutes, uint8_t *hours, uint8_t *day_of_week, uint8_t *day,
                     uint8_t *month, uint8_t *year);
bool ds3231_set_time(uint8_t seconds, uint8_t minutes, uint8_t hours, uint8_t day_of_week, uint8_t day, uint8_t month,
                     uint8_t year);

uint8_t dec_to_bcd(uint8_t val);
uint8_t bcd_to_dec(uint8_t val);
