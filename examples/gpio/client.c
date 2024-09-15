/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <libco.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/gpio/meson/gpio.h>
#include "client.h"
#include "gpio_config.h"

// #define DEBUG_CLIENT

#ifdef DEBUG_CLIENT
#define LOG_CLIENT(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_CLIENT(...) do{}while(0)
#endif
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

void client_main(void) {
    sddf_printf("Setting direction of GPIO1 to output!\n");
    microkit_msginfo msginfo = microkit_msginfo_new(SET_GPIO, 2);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, DIRECTION);
    microkit_mr_set(REQ_GPIO_VALUE_SLOT, DIRECTION_OUTPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set direction of gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_GPIO, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, DIRECTION);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get direction of gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != DIRECTION_OUTPUT) {
        LOG_CLIENT_ERR("problem with direction in driver!\n");
        while (1) {};
    }

    sddf_printf("Setting GPIO1 to on!\n");
    msginfo = microkit_msginfo_new(SET_GPIO, 2);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, OUTPUT);
    microkit_mr_set(REQ_GPIO_VALUE_SLOT, 1);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set output of gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_GPIO, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, OUTPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get output of gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != 1) {
        LOG_CLIENT_ERR("problem with output in driver!\n");
        while (1) {};
    }

    sddf_printf("Setting GPIO1 drive strength to 4000UA!\n");
    msginfo = microkit_msginfo_new(SET_GPIO, 2);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, DRIVE_STRENGTH);
    microkit_mr_set(REQ_GPIO_VALUE_SLOT, DS_4000UA);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set output of gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_GPIO, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, DRIVE_STRENGTH);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get drive strength of gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != DS_4000UA) {
        LOG_CLIENT_ERR("problem with output in driver!\n");
        while (1) {};
    }

    delay_ms(3000);

    sddf_printf("Setting GPIO1 to off!\n");
    msginfo = microkit_msginfo_new(SET_GPIO, 2);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, OUTPUT);
    microkit_mr_set(REQ_GPIO_VALUE_SLOT, 0);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set output of gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_GPIO, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, OUTPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get output of gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != 0) {
        LOG_CLIENT_ERR("problem with output in driver!\n");
        while (1) {};
    }

    sddf_printf("Setting direction of GPIO2 to input!\n");
    msginfo = microkit_msginfo_new(SET_GPIO, 2);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, DIRECTION);
    microkit_mr_set(REQ_GPIO_VALUE_SLOT, DIRECTION_INPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set direction of gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_GPIO, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, DIRECTION);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get direction of gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != DIRECTION_INPUT) {
        LOG_CLIENT_ERR("problem with direction in driver!\n");
        while (1) {};
    }

    sddf_printf("Setting pull of GPIO2 to down!\n");
    msginfo = microkit_msginfo_new(SET_GPIO, 2);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, PULL);
    microkit_mr_set(REQ_GPIO_VALUE_SLOT, PULL_DOWN);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set pull of gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_GPIO, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, PULL);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get pull of gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != PULL_DOWN) {
        LOG_CLIENT_ERR("problem with pull in driver!\n");
        while (1) {};
    }

    sddf_printf("Setting an irq channel to be for GPIO2!\n");
    msginfo = microkit_msginfo_new(SET_IRQ, 2);
    microkit_mr_set(REQ_IRQ_CONFIG_SLOT, PIN);
    microkit_mr_set(REQ_IRQ_VALUE_SLOT, GPIO_2);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set irq channel for gpio with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_IRQ, 1);
    microkit_mr_set(REQ_GPIO_CONFIG_SLOT, PIN);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get pull irq channel for gpio with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != GPIO_2) {
        LOG_CLIENT_ERR("problem with pin setting for channels in driver!\n");
        while (1) {};
    }

    sddf_printf("Setting an irq channel to be rising edge!\n");
    msginfo = microkit_msginfo_new(SET_IRQ, 2);
    microkit_mr_set(REQ_IRQ_CONFIG_SLOT, EDGE);
    microkit_mr_set(REQ_IRQ_VALUE_SLOT, RISING);
    irqedge_msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, irqedge_msginfo);
    if (microkit_msginfo_get_label(irqedge_msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to set edge for irq channel with error %d!\n", error);
        while (1) {};
    }

    sddf_printf("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GET_IRQ, 1);
    microkit_mr_set(REQ_IRQ_CONFIG_SLOT, EDGE);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == FAILURE) {
        size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
        LOG_CLIENT_ERR("failed to get edge for irq channel with error %d!\n", error);
        while (1) {};
    }

    size_t value = microkit_mr_get(RES_GPIO_VALUE_SLOT);
    if (value != RISING) {
        LOG_CLIENT_ERR("problem with pull in driver!\n");
        while (1) {};
    }

    bool led_on = false;
    // this loop receives a irq to turn off and on led!
    sddf_printf("Button now ready to be pressed!\n");
    sddf_printf("This is super prone to breaking so dont spam!\n");
    while (true) {
        co_switch(t_event);

        // recieved irq!
        msginfo = microkit_msginfo_new(SET_GPIO, 2);
        microkit_mr_set(REQ_GPIO_CONFIG_SLOT, OUTPUT);

        if (led_on) {
            // turn off
            microkit_mr_set(REQ_GPIO_VALUE_SLOT, 0);
        } else {
            // turn on
            microkit_mr_set(REQ_GPIO_VALUE_SLOT, 1);
        }
        msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
        if (microkit_msginfo_get_label(msginfo) == FAILURE) {
            size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
            LOG_CLIENT_ERR("failed to set output of gpio with error %d!\n", error);
            while (1) {};
        }
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

    /* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch) {
    switch (ch) {
    case GPIO_DRIVER_CH_1:
        LOG_CLIENT_ERR("We should not of received IRQ from channel 0x%x!\n", ch);
        break;
    case GPIO_DRIVER_CH_2:
        co_switch(t_main);
        break;
    case TIMER_CH:
        co_switch(t_main);
        break;
    default:
        LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
