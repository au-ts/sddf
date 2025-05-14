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

#define DEBUG_CLIENT

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
    LOG_CLIENT("Client Main!\n");
    microkit_msginfo msginfo;
    size_t value;

    LOG_CLIENT("Setting direction of GPIO1 to output!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, GPIO_DIRECTION_OUTPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set direction of gpio with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get direction of gpio with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != GPIO_DIRECTION_OUTPUT) {
        LOG_CLIENT_ERR("problem with direction in driver!\n");
        while (1) {};
    }

    LOG_CLIENT("Setting GPIO1 to on!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get output of gpio with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != 0) {
        LOG_CLIENT_ERR("problem with output in driver!\n");
        while (1) {};
    }

    LOG_CLIENT("Setting GPIO1 drive strength to 4000UA!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_DRIVE_STRENGTH);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, MESON_GPIO_DS_4000UA);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_DRIVE_STRENGTH);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get drive strength of gpio with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != MESON_GPIO_DS_4000UA) {
        LOG_CLIENT_ERR("problem with output in driver!\n");
        while (1) {};
    }

    LOG_CLIENT("Setting GPIO1 to off!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get output of gpio with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != 0) {
        LOG_CLIENT_ERR("problem with output in driver!\n");
        while (1) {};
    }

    LOG_CLIENT("Setting direction of GPIO2 to input!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, GPIO_DIRECTION_INPUT);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set direction of gpio with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_DIRECTION);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get direction of gpio with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != GPIO_DIRECTION_INPUT) {
        LOG_CLIENT_ERR("problem with direction in driver!\n");
        while (1) {};
    }

    LOG_CLIENT("Setting pull of GPIO2 to down!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_PULL);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, MESON_GPIO_NO_PULL);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set pull of gpio with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_PULL);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get pull of gpio with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != MESON_GPIO_NO_PULL) {
        LOG_CLIENT_ERR("problem with pull in driver!\n");
        while (1) {};
    }

    LOG_CLIENT("Setting gpio2s irq channel to be rising edge!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_IRQ, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_IRQ_EDGE);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, MESON_GPIO_IRQ_RISING);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set edge for irq channel with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_IRQ, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_IRQ_EDGE);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get edge for irq channel with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != MESON_GPIO_IRQ_RISING) {
        LOG_CLIENT_ERR("problem with pull in driver! %ld\n", value);
        while (1) {};
    }

    LOG_CLIENT("Setting gpio2s irq channel to have a filter!\n");
    msginfo = microkit_msginfo_new(GPIO_SET_IRQ, 2);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_IRQ_FILTER);
    microkit_mr_set(GPIO_REQ_VALUE_SLOT, MESON_GPIO_IRQ_FILTER_2331NS);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to set filter for irq channel with error %ld!\n", error);
        while (1) {};
    }

    LOG_CLIENT("Checking with get request!\n");
    msginfo = microkit_msginfo_new(GPIO_GET_IRQ, 1);
    microkit_mr_set(GPIO_REQ_CONFIG_SLOT, MESON_GPIO_IRQ_FILTER);
    msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
        size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
        LOG_CLIENT_ERR("failed to get filter for irq channel with error %ld!\n", error);
        while (1) {};
    }

    value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    if (value != MESON_GPIO_IRQ_FILTER_2331NS) {
        LOG_CLIENT_ERR("problem with filter in driver!\n");
        while (1) {};
    }

    bool led_on = false;
    LOG_CLIENT("Button now ready to be pressed!\n");
    while (true) {
        LOG_CLIENT("Waiting for IRQ from driver!\n");
        co_switch(t_event);
        LOG_CLIENT("Received!\n");

        // recieved irq!
        msginfo = microkit_msginfo_new(GPIO_SET_GPIO, 2);
        microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_OUTPUT);

        if (led_on) {
            // turn off
            LOG_CLIENT("Turned off!\n");
            microkit_mr_set(GPIO_REQ_VALUE_SLOT, 0);
            led_on = false;
        } else {
            // turn on
            LOG_CLIENT("Turned on!\n");
            microkit_mr_set(GPIO_REQ_VALUE_SLOT, 1);
            led_on = true;
        }

        msginfo = microkit_ppcall(GPIO_DRIVER_CH_1, msginfo);
        if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
            size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
            LOG_CLIENT_ERR("failed to set output of gpio with error %ld!\n", error);
            while (1) {};
        }
    }

    /* Polling Loop , instead of IRQ based */
    // while (1) {
    //     msginfo = microkit_msginfo_new(GPIO_GET_GPIO, 1);
    //     microkit_mr_set(GPIO_REQ_CONFIG_SLOT, GPIO_INPUT);
    //     msginfo = microkit_ppcall(GPIO_DRIVER_CH_2, msginfo);
    //     if (microkit_msginfo_get_label(msginfo) == GPIO_FAILURE) {
    //         size_t error = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    //         LOG_CLIENT_ERR("failed to get input of gpio with error %ld!\n", error);
    //         while (1) {};
    //     }
    //     value = microkit_mr_get(GPIO_RES_VALUE_SLOT);
    //     LOG_CLIENT("%ld!\n", value);
    // }
    // while(1){}
}

void init(void) {
    LOG_CLIENT("Init\n");

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
        default:
            LOG_CLIENT_ERR("Unknown channel 0x%x!\n", ch);
    }
}
