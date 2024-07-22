#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include "ds3231.h"
#include "client.h"

// #define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("DS3231_CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("DS3231_CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

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

// Function to convert decimal to BCD
uint8_t decToBcd(uint8_t val) {
  return ((val / 10 * 16) + (val % 10));
}

// Function to convert BCD to decimal
uint8_t bcdToDec(uint8_t val) {
  return ((val / 16 * 10) + (val % 16));
}

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

void client_main(void) {
    LOG_CLIENT("client_main: started\n");

    LOG_CLIENT("see if ds3231 responds with ACK\n");
    uint8_t write_fail = ds3231_write(NULL, 0, DEFAULT_READ_ACK_FRAME_RETRIES);
    if (write_fail) {
        LOG_CLIENT_ERR("failed to find DS3231 on bus!\n");
        while (1) {};
    }

    // Set the time
    uint8_t intial_second = 42;
    uint8_t intial_minute = 59;
    uint8_t intial_hour = 23;
    uint8_t intial_day_of_week = 7;
    uint8_t intial_day = 31;
    uint8_t intial_month = 12;
    uint8_t intial_year = 23;

    uint8_t set_time_buffer[8];
    set_time_buffer[0] = DS3231_REGISTER_SECONDS; // Address to start writing at
    set_time_buffer[1] = decToBcd(intial_second);
    set_time_buffer[2] = decToBcd(intial_minute);
    set_time_buffer[3] = decToBcd(intial_hour);
    set_time_buffer[4] = decToBcd(intial_day_of_week);
    set_time_buffer[5] = decToBcd(intial_day);
    set_time_buffer[6] = decToBcd(intial_month);
    set_time_buffer[7] = decToBcd(intial_year);
    write_fail = ds3231_write(set_time_buffer, 8, DEFAULT_READ_ACK_FRAME_RETRIES);
    if (write_fail) {
        LOG_CLIENT_ERR("failed to set time on DS3231 on bus!\n");
        while (1) {};
    }
    sddf_printf("Set Date and Time on DS3231 to: %02d-%02d-%02d %02d:%02d:%02d (%s)\n", intial_day, intial_month, intial_year, intial_hour, intial_minute, intial_second, day_of_week_strings[intial_day_of_week - 1]);

    LOG_CLIENT("Starting to ask for the time!\n");
    while (true) {
        LOG_CLIENT("Tell DS3231 what register to start reading from!\n");
        uint8_t start_register_write_buffer[1];
        start_register_write_buffer[0] = DS3231_REGISTER_SECONDS; // to tell ds3231 to start reading at register 0
        write_fail = ds3231_write(start_register_write_buffer, 1, DEFAULT_READ_ACK_FRAME_RETRIES);
        if (write_fail) {
            LOG_CLIENT_ERR("failed to tell DS3231 the correct starting register to read from!\n");
            while (1) {};
        }

        LOG_CLIENT("Make read time request!\n");
        uint8_t time_response_buffer[7];
        uint8_t read_fail = ds3231_read(time_response_buffer, 7, DEFAULT_READ_RESPONSE_RETRIES);
        if (read_fail) {
            LOG_CLIENT_ERR("failed to read response for getting the time\n");
            while (1) {};
        }
        uint8_t second = bcdToDec(time_response_buffer[0]);
        uint8_t minute = bcdToDec(time_response_buffer[1]);
        uint8_t hour = bcdToDec(time_response_buffer[2]);
        uint8_t day_of_week = bcdToDec(time_response_buffer[3]);
        uint8_t day = bcdToDec(time_response_buffer[4]);
        uint8_t month = bcdToDec(time_response_buffer[5] & (~(1 << DS3231_BIT_CENTURY))); // mask out the century 
        uint8_t year = bcdToDec(time_response_buffer[6]);

        sddf_printf("Date and Time: %02d-%02d-%02d %02d:%02d:%02d (%s)\n", day, month, year, hour, minute, second, day_of_week_strings[day_of_week - 1]);

        delay_ms(500);
    }
}

bool delay_ms(size_t milliseconds) {
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

void init(void) {
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

void notified(microkit_channel ch) {
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