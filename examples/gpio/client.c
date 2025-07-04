/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <libco.h>
#include <sddf/gpio/client.h>
#include <sddf/gpio/config.h>
#include <sddf/util/printf.h>
#include <os/sddf.h>
#include <gpio_config.h>

__attribute__((__section__(".gpio_client_config"))) gpio_client_config_t config;

// @ Tristan : will need to change this
microkit_channel gpio_channel_1_output;
microkit_channel gpio_channel_2_input;

cothread_t t_event;
cothread_t t_main;

#define STACK_SIZE (4096)
static char t_client_main_stack[STACK_SIZE];

#define USE_POLLING 

static inline void polling_based()
{
	while (1) {}
}

static inline void irq_based()
{
	while (1) {}
}

void client_main(void)
{


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

	// sddf_printf("CLIENT|INFO: Is gpio_driver_channel_mappings included : %d\n", gpio_driver_channel_mappings[0].pin);
	// sddf_ppcall(gpio_channel_1_output, seL4_MessageInfo_new(2, 0, 0, 1));
	// sddf_ppcall(gpio_channel_2_input, seL4_MessageInfo_new(3, 0, 0, 1));
}

// @ TRistan : add coroutines later
void notified(microkit_channel ch)
{
    if (ch == gpio_channel_2_input) {
    	sddf_printf("CLIENT|INFO: Got an interupt from GPIO!\n"); 
    	co_switch(t_main);
    } else {
    	sddf_printf("CLIENT|ERROR: Unknown channel!\n"); 
    }
}