/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <sddf/i2c/devices/ds3231/ds3231.h>
#include "client.h"

// #define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("DS3231_CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("DS3231_CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


#define DS_3231_ON

#ifdef DS_3231_ON
#define USING_HALT(...) do{}while(0)
#else
#define USING_HALT(...) do{ while(1); }while(0)
#endif

uintptr_t data_region;
uintptr_t request_region;
uintptr_t response_region;
i2c_queue_handle_t queue;

cothread_t t_event;
cothread_t t_main;

#define DEFAULT_READ_RESPONSE_RETRIES (256)
#define DEFAULT_READ_ACK_FRAME_RETRIES (20)

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

// weeks bits are from 1 - 7 so remember to index correctly (subtract 1)
static const char *day_of_week_strings[] = {
    "Monday",
    "Tuesday",
    "Wednesday",
    "Thursday",
    "Friday",
    "Saturday",
    "Sunday"
};

void client_main(void)
{
    USING_HALT();

    LOG_CLIENT("client_main: started\n");

    LOG_CLIENT("see if ds3231 responds with ACK\n");
    uint8_t write_fail = ds3231_write(NULL, 0, DEFAULT_READ_ACK_FRAME_RETRIES);
    if (write_fail) {
        LOG_CLIENT_ERR("failed to find DS3231 on bus!\n");
        assert(false);
    }

    if (ds3231_set_time(42, 59, 23, 7, 31, 12, 23)) {
        LOG_CLIENT_ERR("failed to set time on DS3231!\n");
        assert(false);
    }
    sddf_printf("Set Date and Time on DS3231 to: %02d-%02d-%02d %02d:%02d:%02d (%s)\n", 31, 12, 23, 23, 59, 42,
                day_of_week_strings[7 - 1]);

    LOG_CLIENT("Starting to ask for the time!\n");
    while (true) {
        uint8_t second;
        uint8_t minute;
        uint8_t hour;
        uint8_t day_of_week;
        uint8_t day;
        uint8_t month;
        uint8_t year;
        if (ds3231_get_time(&second, &minute, &hour, &day_of_week, &day, &month, &year)) {
            LOG_CLIENT_ERR("failed to get time from DS3231!\n");
            assert(false);
        }

        if (day_of_week < 1 || day_of_week > 7) {
            LOG_CLIENT_ERR("day of week index is wrong\n");
            sddf_printf("Date and Time: %02d-%02d-%02d %02d:%02d:%02d\n", day, month, year, hour, minute, second);
            delay_ms(500);
            continue;
        }

        sddf_printf("Date and Time: %02d-%02d-%02d %02d:%02d:%02d (%s)\n", day, month, year, hour, minute, second,
                    day_of_week_strings[day_of_week - 1]);

        delay_ms(500);
    }
}

bool delay_ms(size_t milliseconds)
{
    size_t time_ns = milliseconds * NS_IN_MS;

    /* Detect potential overflow */
    if (milliseconds != 0 && time_ns / milliseconds != NS_IN_MS) {
        LOG_CLIENT_ERR("overflow detected in delay_ms");
        return false;
    }

    sddf_timer_set_timeout(TIMER_CH, time_ns);
    co_switch(t_event);

    return true;
}

void init(void)
{
    LOG_CLIENT("init\n");

    queue = i2c_queue_init((i2c_queue_t *) request_region, (i2c_queue_t *) response_region);

    bool claimed = i2c_bus_claim(I2C_VIRTUALISER_CH, DS3231_I2C_BUS_ADDRESS);
    if (!claimed) {
        LOG_CLIENT_ERR("failed to claim DS3231 bus\n");
        return;
    }
    LOG_CLIENT("claimed DS3231 bus!\n");

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case I2C_VIRTUALISER_CH:
        co_switch(t_main);
        break;
    case TIMER_CH:
        co_switch(t_main);
        break;
    default:
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}