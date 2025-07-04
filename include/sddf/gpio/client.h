/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/gpio/protocol.h>

// /**
//  * Request a timeout via PPC into the passive timer driver.
//  * Use the label to indicate this request.
//  * @param microkit channel of timer driver.
//  * @param timeout relative timeout in nanoseconds.
//  */
// static inline void sddf_timer_set_timeout(unsigned int channel, uint64_t timeout)
// {
//     sddf_set_mr(0, timeout);
//     sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_TIMER_SET_TIMEOUT, 0, 0, 1));
// }

// /**
//  * Request the time since start up via PPC into the passive timer driver.
//  * Use the label to indicate this request.
//  * @param microkit channel of timer driver.
//  * @return the time in nanoseconds since start up.
//  */
// static inline uint64_t sddf_timer_time_now(unsigned int channel)
// {
//     sddf_ppcall(channel, seL4_MessageInfo_new(SDDF_TIMER_GET_TIME, 0, 0, 0));
//     uint64_t time_now = sddf_get_mr(0);
//     return time_now;
// }

static inline int sddf_gpio_get_value(unsigned int channel) {
	return -1;
}

static inline int sddf_gpio_set_value(unsigned int channel, uint32_t value) {
	return -1;
}

static inline int sddf_gpio_get_direction(unsigned int channel) {
	return -1;
}

static inline int sddf_gpio_set_direction(unsigned int channel, GPIO_direction_t direction) {
	return -1;
}

static inline int sddf_gpio_get_irq_configuration(unsigned int channel) {
	return -1;
}

static inline int sddf_gpio_set_irq_configuration(unsigned int channel, GPIO_irq_configuration_t config, uint32_t value) {
	(void)value;
	return -1;
}

static inline int sddf_gpio_get_pin_configuration(unsigned int channel) {
	(void)channel;
	return -GPIO_ERROR_NOT_IMPLEMENTED;
}

static inline int sddf_gpio_set_pin_configuration(unsigned int channel, GPIO_pin_configuration_t config, uint32_t value) {
	(void)channel;
	(void)config;
	(void)value;
	return -GPIO_ERROR_NOT_IMPLEMENTED;
}


// how do we convey that its an erro
// we could just return -1 and still have it as an int ?

// errors can be negative and if its works its positive

// 