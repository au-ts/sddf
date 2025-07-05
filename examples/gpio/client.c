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

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#define USE_POLLING 

static inline void polling_based()
{	
	int ret = 0;

	sddf_printf("CLIENT|INFO: Starting Polling!\n");
	int input = 0; // assuming it starts with no input (pin floating low or pulled down)

	sddf_printf("CLIENT|INFO: Press button when ready!\n");
	while (1) {
		ret = sddf_gpio_get(gpio_channel_2_input);
		if (ret < 0) {
			sddf_printf("CLIENT|ERROR: Failed to get value. Error code : %d!\n", ret); 
			while (1) {}
		}

		if (input != ret) {
			// the charge/state of the pin changed thus we should flip the output to the LED
			ret = sddf_gpio_set(gpio_channel_1_output, ret);
			if (ret < 0) {
				sddf_printf("CLIENT|ERROR: Failed to set value. Error code : %d!\n", ret); 
				while (1) {}
			}
			input = ret;
		}
	}
}

static inline void irq_based()
{
	int ret = 0;

	sddf_printf("CLIENT|INFO: Enabling IRQ!\n"); 
	ret = sddf_gpio_irq_enable(gpio_channel_2_input);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to enable IRQ. Error code : %d!\n", ret); 
		while (1) {}
	}
	
	sddf_printf("CLIENT|INFO: Setting type of IRQ!\n"); 
	// We choose SDDF_IRQ_TYPE_EDGE_BOTH to emulate the polling loop above.
	ret = sddf_gpio_irq_set_type(gpio_channel_2_input, SDDF_IRQ_TYPE_EDGE_BOTH);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set IRQ type. Error code : %d!\n", ret); 
		while (1) {}
	}

	sddf_printf("CLIENT|INFO: Starting IRQ driven loop!\n"); 

	// We set it to 1 before
	int output = 1;

	sddf_printf("CLIENT|INFO: Press button when ready!\n");
    while (1) {
        sddf_printf("Waiting for IRQ from driver!\n");

        co_switch(t_event);

        // change the output
        output = output == 1 ? 0 : 1;

        ret = sddf_gpio_set(gpio_channel_1_output, ret);
		if (ret < 0) {
			sddf_printf("CLIENT|ERROR: Failed to set value. Error code : %d!\n", ret); 
			while (1) {}
		}

        if (output == 0) {
            sddf_printf("Turned off LED!\n");
        } else if (output == 1) {
            sddf_printf("Turned on LED!\n");
        }
    }
}

void client_main(void)
{
	int ret = 0;

	sddf_printf("CLIENT|INFO: Setting direction of gpio channel 1 to output!"); 
	ret = sddf_gpio_direction_output(gpio_channel_1_output, 0);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set direction to output. Error code : %d!\n", ret); 
		while (1) {}
	}
	
	sddf_printf("CLIENT|INFO: Setting direction of gpio channel 1 to input!"); 
	ret = sddf_gpio_direction_input(gpio_channel_2_input);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set direction to input. Error code : %d!\n", ret); 
		while (1) {}
	}
	
	sddf_printf("CLIENT|INFO: Setting value of gpio channel 1 to 1, LED should switch on!"); 	
	ret = sddf_gpio_set(gpio_channel_1_output, 1);
	if (ret < 0) {
		sddf_printf("CLIENT|ERROR: Failed to set value. Error code : %d!\n", ret); 
		while (1) {}
	}
	
	// TODO: should specify to users if they need to they need to set as pull up or pull down
	// or at least do it externally for the input pin.

#ifdef USE_POLLING
	polling_based();
#else
	irq_based();
#endif	
}

void init(void)
{
	sddf_printf("CLIENT|INFO: starting\n");

	assert(gpio_config_check_magic(&config));

	gpio_channel_1_output = config.driver_channel_ids[0];
	gpio_channel_2_input = config.driver_channel_ids[1];

	/* Define the event loop/notified thread as the active co-routine */
    t_event = co_active();

    /* derive main entry point */
    t_main = co_derive((void *)t_client_main_stack, STACK_SIZE, client_main);

    co_switch(t_main);
}

void notified(microkit_channel ch)
{
    if (ch == gpio_channel_1_output) {
    	sddf_printf("CLIENT|ERROR: We should not of received IRQ from this channel!\n"); 
    } else if (ch == gpio_channel_2_input) {
    	sddf_printf("CLIENT|INFO: Got an interupt from GPIO!\n"); 
    	co_switch(t_main);
    } else {
    	sddf_printf("CLIENT|ERROR: Unknown channel?!\n"); 
    }
}