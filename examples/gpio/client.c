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
#include <os/sddf.h>
#include <gpio_config.h>

__attribute__((__section__(".gpio_client_config"))) gpio_client_config_t config;

microkit_channel gpio_channel_1_output;
microkit_channel gpio_channel_2_input;
microkit_channel gpio_channel_3_output;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

// #define USE_POLLING

static inline void print_instructions() {
	sddf_printf("\nCLIENT|INFO: Connect PIN2 to PIN3 to turn on the LED!\n");
	sddf_printf("CLIENT|INFO: Disconnect PIN2 to PIN3 to turn off the LED!\n\n");
}

static inline void polling_based()
{
	int ret = 0;

	sddf_printf("\nCLIENT|INFO: Starting Polling!\n");

	print_instructions();

	while (1) {
		ret = sddf_gpio_get(gpio_channel_2_input);
		if (ret < 0) {
			sddf_printf("CLIENT|ERROR: Failed to get value. Error code : %d!\n", ret);
			while (1) {}
		}

		ret = sddf_gpio_set(gpio_channel_1_output, ret);
		if (ret < 0) {
			sddf_printf("CLIENT|ERROR: Failed to set value. Error code : %d!\n", ret);
			while (1) {}
		}
	}
}

static inline void irq_based()
{
	int ret = 0;

	sddf_printf("CLIENT|INFO: Setting type of IRQ!\n");
	// We choose SDDF_IRQ_TYPE_EDGE_BOTH to emulate the polling loop above.
	ret = sddf_gpio_irq_set_type(gpio_channel_2_input, SDDF_IRQ_TYPE_EDGE_BOTH);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set IRQ type. Error code : %d!\n", ret);
		while (1) {}
	}

	sddf_printf("CLIENT|INFO: Enabling IRQ!\n");
	ret = sddf_gpio_irq_enable(gpio_channel_2_input);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to enable IRQ. Error code : %d!\n", ret);
		while (1) {}
	}

	sddf_printf("\nCLIENT|INFO: Starting IRQ driven loop!\n");

	print_instructions();

	// Initially off
	int output = 0;

    while (1) {
    	// Waiting of irq from driver
        co_switch(t_event);

        // change the output
        output = output == 1 ? 0 : 1;

        ret = sddf_gpio_set(gpio_channel_1_output, output);
		if (ret < 0) {
			sddf_printf("CLIENT|ERROR: Failed to set value. Error code : %d!\n", ret); 
			while (1) {}
		}
    }
}

void client_main(void)
{
	sddf_printf("CLIENT|INFO: Initial state instructions:\n"
		"  GPIO_1 should be attached to resistors then an LED then Ground.\n"
		"  GPIO_2 should start unattached to anything.\n"
		"  NOTE: for this example this pin should have a floating logical state of 0 or a pull down resistor attached.\n"
		"  GPIO_3 should start unattached to anythng.!\n\n");

	sddf_printf("CLIENT|INFO: Other infomation:\n"
		"  NOTE: there are 2 modes you can use, polling and irq_based which can be changed with #define USE_POLLING\n"
		"  NOTE: there is no debounce logic so it might not appear to work for the IRQ based loop\n\n");

	int ret = 0;
	sddf_printf("CLIENT|INFO: Setting direction of gpio channel 1 to output!\n");
	ret = sddf_gpio_direction_output(gpio_channel_1_output, 0);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set direction to output. Error code : %d!\n", ret);
		while (1) {}
	} 

	sddf_printf("CLIENT|INFO: Setting direction of gpio channel 2 to input!\n");
	ret = sddf_gpio_direction_input(gpio_channel_2_input);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set direction to input. Error code : %d!\n", ret);
		while (1) {}
	}

	sddf_printf("CLIENT|INFO: Setting direction of gpio channel 3 to output!\n");
	ret = sddf_gpio_direction_output(gpio_channel_3_output, 1);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set direction to output. Error code : %d!\n", ret);
		while (1) {}
	}

#ifdef USE_POLLING
	polling_based();
#else
	irq_based();
#endif
}

void init(void)
{
	sddf_dprintf("\nCLIENT|INFO: Starting\n\n");

	assert(gpio_config_check_magic(&config));

	gpio_channel_1_output = config.driver_channel_ids[0];
	gpio_channel_2_input = config.driver_channel_ids[1];
	gpio_channel_3_output = config.driver_channel_ids[2];

	// Define the event loop/notified thread as the active co-routine
    t_event = co_active();

    // derive main entry point
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch)
{
    if (ch == gpio_channel_1_output) {
    	sddf_printf("CLIENT|ERROR: We should not of received IRQ from this channel! (channel : %d)\n", ch);
    } else if (ch == gpio_channel_2_input) {
    	sddf_printf("CLIENT|INFO: Got an interupt from GPIO driver!\n");
    	co_switch(t_main);
    } else if (ch == gpio_channel_3_output) {
    	sddf_printf("CLIENT|ERROR: We should not of received IRQ from this channel! (channel : %d)\n", ch);
    } else {
    	sddf_printf("CLIENT|ERROR: Unknown channel?!\n");
    }
}