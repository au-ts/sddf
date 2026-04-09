/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/fence.h>
#include <sddf/util/printf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <sddf/i2c/config.h>
#include <sddf/i2c/libi2c.h>

#define LOG_CLIENT(...) do{ sddf_printf("INA219|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("INA219|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

bool delay_ms(size_t milliseconds);

__attribute__((__section__(".i2c_client_config"))) i2c_client_config_t i2c_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;
__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

static serial_queue_handle_t serial_tx_queue_handle;

i2c_queue_handle_t queue;
uintptr_t data_region;
libi2c_conf_t libi2c_conf;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#ifndef I2C_DATA_REGION
#define I2C_DATA_REGION ((uint8_t *)i2c_config.data.vaddr)
#endif

#define INA219_ADDR                 (0x44)  // 3v3 rail
#define INA219_CONFIG_ADDR          (0x0)
#define INA219_SHUNT_V_ADDR         (0x1)
#define INA219_BUS_V_ADDR           (0x2)
#define INA219_POWER_ADDR           (0x3)
#define INA219_CURRENT_ADDR         (0x4)
#define INA219_CALIBRATION_ADDR     (0x5)

// Constants for genesys2
// beware endianness!
const uint8_t config[2] = { 0x08, 0x67 };
const uint8_t calibration[2] = { 0x40, 0x00 };

void client_main(void)
{
    volatile uint8_t *data = (volatile uint8_t *)data_region;

    // Kick I2C bus before doing anything.
    sddf_i2c_write(&libi2c_conf, 0x1, data, 1);
    delay_ms(100);

    // Initial: reset, then program registers.
    memcpy((volatile uint8_t *)(data + 1), config, 2);
    data[0] = INA219_CONFIG_ADDR;
    assert(sddf_i2c_write(&libi2c_conf, INA219_ADDR, data, 3) == 0);

    memcpy((volatile uint8_t *)(data + 1), calibration, 2);
    data[0] = INA219_CALIBRATION_ADDR;
    assert(sddf_i2c_write(&libi2c_conf, INA219_ADDR, data, 3) == 0);

    // BRNG value for bus voltage range. Config reg bit 13
    uint8_t brng = ((config[1] & (0b100000)) >> 5) & 0x1;

    while (true) {
        // Read current, voltage and power
        uint16_t voltage, power, current;
        assert(sddf_i2c_writeread(&libi2c_conf, INA219_ADDR, INA219_BUS_V_ADDR, data, 2) == 0);

        // Low 3 bits of voltage reg are control bits
        voltage = ((data[0] << 8) | data[1]) >> 3;
        // Range = 32V if brng=1, else 16V
        double voltage_human_readable = ((double)voltage / (0x1FFF)) * (16 * (1 + brng));
        assert(sddf_i2c_writeread(&libi2c_conf, INA219_ADDR, INA219_CURRENT_ADDR, data, 2) == 0);

        current = (uint16_t)((data[0] << 8) | data[1]);
        assert(sddf_i2c_writeread(&libi2c_conf, INA219_ADDR, INA219_POWER_ADDR, data, 2) == 0);
        power = ((data[0] << 8) | data[1]);

        LOG_CLIENT("Measurement completed!\n");
        LOG_CLIENT("\tBus voltage = %fV\n", voltage_human_readable);
        LOG_CLIENT("\tCurrent = %u\n", current);
        LOG_CLIENT("\tPower= %u\n", power);
        delay_ms(5000);
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

    sddf_timer_set_timeout(timer_config.driver_id, time_ns);
    co_switch(t_event);

    return true;
}

void init(void)
{
    assert(serial_config_check_magic(&serial_config));
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

    assert(i2c_config_check_magic((void *)&i2c_config));

    data_region = (uintptr_t)i2c_config.data.vaddr;
    queue = i2c_queue_init(i2c_config.virt.req_queue.vaddr, i2c_config.virt.resp_queue.vaddr);

    // Claim all addresses except the general call address (0)
    for (uint8_t i = 1; i < (1 << 7); i++) {
        bool claimed = i2c_bus_claim(i2c_config.virt.id, i);
        if (!claimed) {
            LOG_CLIENT_ERR("failed to claim %u!\n", i);
            return;
        }
    }

    /* Initialise libi2c */
    libi2c_init(&libi2c_conf, &queue);

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch)
{
    if (ch == i2c_config.virt.id || ch == timer_config.driver_id) {
        co_switch(t_main);
    } else if (ch == serial_config.tx.id) {
        // Nothing to do
    } else {
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
