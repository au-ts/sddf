/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <libco.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/gpio/protocol.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <os/sddf.h>
#include <gpio_config.h>

#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

__attribute__((__section__(".gpio_client_config"))) gpio_client_config_t gpio_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

microkit_channel timer_channel;

microkit_channel gpio_channel_1_output;
microkit_channel gpio_channel_2_input;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

int gpio_irqs_received = 0;

void client_main(void)
{
    LOG_CLIENT("Starting GPIO example! Note this GPIO1 must be connected to GPIO2!\n\n");

    int ret = 0;
    LOG_CLIENT("Setting direction of GPIO1 to output and intial value 0!\n");
    ret = sddf_gpio_direction_output(gpio_channel_1_output, 0);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set direction to output. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Setting direction of GPIO2 to input!\n");
    ret = sddf_gpio_direction_input(gpio_channel_2_input);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set direction to input. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Checking (GPIO1's output == GPIO2's input)!\n");
    ret = sddf_gpio_get(gpio_channel_2_input);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to get value. Error code : %d!\n", ret);
        assert(false);
    } else if (ret == 1) {
        LOG_CLIENT_ERR("Failed because GPIO2's input is reading value 1!\n");
        assert(false);
    }

    LOG_CLIENT("Setting value of GPIO1 to 1!\n");
    ret = sddf_gpio_set(gpio_channel_1_output, 1);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Checking (GPIO1's output == GPIO2's input)!\n");
    ret = sddf_gpio_get(gpio_channel_2_input);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to get value. Error code : %d!\n", ret);
        assert(false);
    } else if (ret == 0) {
        LOG_CLIENT_ERR("Failed because GPIO2's input is reading value 0!\n");
        assert(false);
    }

    LOG_CLIENT("Now we will test IRQ functionality!\n");

    LOG_CLIENT("Setting type of IRQ of GPIO2 to falling edge!\n");
    ret = sddf_gpio_irq_set_type(gpio_channel_2_input, SDDF_IRQ_TYPE_EDGE_FALLING);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set IRQ type. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Enabling IRQ functionality for GPIO2!\n");
    ret = sddf_gpio_irq_enable(gpio_channel_2_input);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to enable IRQ. Error code : %d!\n", ret);
        assert(false);
    }

    // To actually test an IRQ was received from a GPIO we set a timeout so that we can check if we got an IRQ
    // from the GPIO driver within a reasonable amount of time.
    LOG_CLIENT("Setting a timeout for 1 second!\n");
    sddf_timer_set_timeout(timer_channel, NS_IN_S);

    LOG_CLIENT("Setting value of GPIO1 to 0!\n");
    ret = sddf_gpio_set(gpio_channel_1_output, 0);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Main coroutine paused!\n");
    co_switch(t_event);
    LOG_CLIENT("Main coroutine resumed!\n");

    LOG_CLIENT("Checking we received irq from GPIO2!\n");
    if (gpio_irqs_received != 1) {
        LOG_CLIENT_ERR("We received wrong amount of IRQs from GPIO2. Amount : %d!\n", gpio_irqs_received);
        assert(false);
    }

    LOG_CLIENT("Setting type of IRQ of GPIO2 to rising edge!\n");
    ret = sddf_gpio_irq_set_type(gpio_channel_2_input, SDDF_IRQ_TYPE_EDGE_RISING);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set IRQ type. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Re-enabling IRQ functionality for GPIO2!\n");
    ret = sddf_gpio_irq_enable(gpio_channel_2_input);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to enable IRQ. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Setting a timeout for 1 second!\n");
    sddf_timer_set_timeout(timer_channel, NS_IN_S);

    LOG_CLIENT("Setting value of GPIO1 to 1!\n");
    ret = sddf_gpio_set(gpio_channel_1_output, 1);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Main coroutine paused!\n");
    co_switch(t_event);
    LOG_CLIENT("Main coroutine resumed!\n");

    LOG_CLIENT("Checking we received irq from GPIO2!\n");
    if (gpio_irqs_received != 2) {
        LOG_CLIENT_ERR("We received wrong amount of IRQs from GPIO2. Amount : %d!\n", gpio_irqs_received);
        assert(false);
    }

    LOG_CLIENT("Re-enabling IRQ functionality for GPIO2!\n");
    ret = sddf_gpio_irq_enable(gpio_channel_2_input);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to enable IRQ. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Setting a timeout for 1 second!\n");
    sddf_timer_set_timeout(timer_channel, NS_IN_S);

    LOG_CLIENT("Setting value of GPIO1 to 0!\n");
    ret = sddf_gpio_set(gpio_channel_1_output, 0);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Main coroutine paused!\n");
    co_switch(t_event);
    LOG_CLIENT("Main coroutine resumed!\n");

    LOG_CLIENT("Checking we DIDN'T recieve irq from GPIO2!\n");
    if (gpio_irqs_received != 2) {
        LOG_CLIENT_ERR("We received wrong amount of IRQs from GPIO2. Amount : %d!\n", gpio_irqs_received);
        assert(false);
    }

    LOG_CLIENT("Setting type of IRQ of GPIO2 to high level!\n");
    ret = sddf_gpio_irq_set_type(gpio_channel_2_input, SDDF_IRQ_TYPE_LEVEL_HIGH);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set IRQ type. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Setting a timeout for 1 second!\n");
    sddf_timer_set_timeout(timer_channel, NS_IN_S);

    LOG_CLIENT("Checking we havent received any irq's from GPIO2!\n");
    if (gpio_irqs_received != 2) {
        LOG_CLIENT_ERR("We received wrong amount of IRQs from GPIO2. Amount : %d!\n", gpio_irqs_received);
        assert(false);
    }

    LOG_CLIENT("Setting value of GPIO1 to 1!\n");
    ret = sddf_gpio_set(gpio_channel_1_output, 1);
    if (ret < 0) {
        LOG_CLIENT_ERR("Failed to set value. Error code : %d!\n", ret);
        assert(false);
    }

    LOG_CLIENT("Main coroutine paused!\n");
    co_switch(t_event);
    LOG_CLIENT("Main coroutine resumed!\n");

    LOG_CLIENT("Checking we received irq from GPIO2!\n\n");
    if (gpio_irqs_received != 3) {
        LOG_CLIENT_ERR("We received wrong amount of IRQs from GPIO2. Amount : %d!\n", gpio_irqs_received);
        assert(false);
    }

    LOG_CLIENT("IF YOU GOT THIS FAR EVERYTHING WENT SMOOTHLY!!!\n");

    while (1) {}
}

void init(void)
{
    LOG_CLIENT("Client Init!\n\n");

    assert(gpio_config_check_magic(&gpio_config));
    assert(timer_config_check_magic(&timer_config));

    gpio_channel_1_output = gpio_config.driver_channel_ids[0];
    gpio_channel_2_input = gpio_config.driver_channel_ids[1];

    timer_channel = timer_config.driver_id;

    // Define the event loop/notified thread as the active co-routine
    t_event = co_active();

    // derive main entry point
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch)
{
    if (ch == gpio_channel_1_output) {
        LOG_CLIENT_ERR("We should not have received IRQ from this gpio channel! (channel : %d)\n", ch);
        assert(false);
    } else if (ch == gpio_channel_2_input) {
        LOG_CLIENT("Got an interrupt from GPIO driver!\n");
        gpio_irqs_received++;
    } else if (ch == timer_channel) {
        LOG_CLIENT("Got an interrupt from timer driver!\n");
        co_switch(t_main);
    } else {
        LOG_CLIENT_ERR("Unknown channel?!\n");
        assert(false);
    }
}
