/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <os/sddf.h>
#include <stdint.h>
#include <sddf/gpio/protocol.h>

static inline uint32_t gpio_make_label(uint32_t interface, uint32_t value)
{
    return (interface & SDDF_REQUEST_INTERFACE_MASK) | gpio_encode_value(value);
}

static inline int gpio_check_err(uint32_t label)
{
    if (label & BIT(SDDF_GPIO_RESPONSE_ERROR_BIT)) {
        return -((int)(label & SDDF_GPIO_RESPONSE_VALUE_MASK));
    }
    return 0;
}

// NOTE: GPIO driver is passive

// GPIO_BASED

/**
 * Request the direction of GPIO line associated with channel (from gpio_config.h).
 *
 * @param microkit channel of gpio driver.
 * @return negative error code or direction of GPIO pin (SDDF_GPIO_line_direction_t).
 */
static int sddf_gpio_get_direction(uint32_t channel)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_GET_DIRECTION, 0);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }

    return (label & BIT(0)) ? SDDF_GPIO_LINE_DIRECTION_OUT : SDDF_GPIO_LINE_DIRECTION_IN;
}

/**
 * Request for direction of GPIO line associated with channel (from gpio_config.h) to be an input.
 *
 * @param microkit channel of gpio driver.
 * @return negative error code or 0.
 */
static int sddf_gpio_direction_input(uint32_t channel)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_DIRECTION_INPUT, 0);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

/**
 * Request for direction of GPIO line associated with channel (from gpio_config.h) to be an output with requested intial value.
 *
 * @param microkit channel of gpio driver.
 * @value
 * @return negative error code or 0.
 */
static int sddf_gpio_direction_output(uint32_t channel, uint32_t value)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_DIRECTION_OUTPUT, value);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

/**
 * Request the value of GPIO line associated with channel (from gpio_config.h).
 *
 * @param microkit channel of gpio driver.
 * @return negative error code or value of line.
 */
static int sddf_gpio_get(uint32_t channel)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_GET, 0);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return (label & BIT(0)) ? 1 : 0;
}

/**
 * Request for value of GPIO line associated with channel (from gpio_config.h) to be requested logical level value.
 * This usually updates the output latch so may not actually drive the GPIO line if its still in input mode.
 *
 * @param microkit channel of gpio driver.
 * @param value
 * @return negative error code or 0.
 */
static int sddf_gpio_set(uint32_t channel, uint32_t value)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_SET, value);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

/**
 * Request the configuration of GPIO line associated with channel (from gpio_config.h) to requested config (+ arguement) value(s).
 *
 * @param microkit channel of gpio driver.
 * @param configuration
 * @param optional arguement of config (usually a continuous value rather than flag)
 *
 * @return negative error code or 0.
 */
static int sddf_gpio_set_config(uint32_t channel, uint32_t config, uint32_t argument)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_SET_CONFIG, config);
    sddf_set_mr(0, argument);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 1));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

// IRQ_BASED

/**
 * Request for IRQ line associated with channel (from gpio_config.h) to be enabled.
 *
 * @param microkit channel of gpio driver.
 * @return negative error code or 0.
 */
static int sddf_gpio_irq_enable(uint32_t channel)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_IRQ_ENABLE, 0);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

/**
 * Request for IRQ line associated with channel (from gpio_config.h) to be disabled.
 *
 * @param microkit channel of gpio driver.
 * @return negative error code or 0.
 */
static int sddf_gpio_irq_disable(uint32_t channel)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_IRQ_DISABLE, 0);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

/**
 * Request for type of IRQ line associated with channel (from gpio_config.h) to be requested type .
 *
 * @param microkit channel of gpio driver.
 * @param SDDF_GPIO_irq_line_status_t type.
 * @return negative error code or 0.
 */
static int sddf_gpio_irq_set_type(uint32_t channel, uint32_t type)
{
    uint32_t label = gpio_make_label(SDDF_GPIO_IRQ_SET_TYPE, type);
    microkit_msginfo msginfo = sddf_ppcall(channel, seL4_MessageInfo_new(label, 0, 0, 0));
    label = microkit_msginfo_get_label(msginfo);

    int err = gpio_check_err(label);
    if (err) {
        return err;
    }
    return 0;
}

// NOTE: there is no sddf_gpio_get_config function this is because:
// - Most GPIO controllers don’t let you read back “config” bits
// - Clients can shadow if they really want it

// TODO: changes need to be made to current gpio_config.h file
// static inline int sddf_gpio_get_multiple(uint32_t channel, uint32_t *mask, uint32_t *bits) {
// 	return -1;
// }

// TODO: changes need to be made to current gpio_config.h file
// static inline int sddf_gpio_set_multiple(uint32_t channel, uint32_t *mask, uint32_t *bits) {
// 	return -1;
// }

// tbd...
// static inline int sddf_gpio_set_rv(uint32_t channel, int value) {
// 	return -1;
// }

// tbd...
// static inline int sddf_gpio_set_multiple_rv(uint32_t channel, unsigned int *mask, uint32_t *bits) {
// 	return -1;
// }

// tbd...
// static inline int sddf_gpio_en_hw_timestamp(uint32_t channel, uint32_t flags) {
// 	return -1;
// }

// tbd...
// static inline int sddf_gpio_dis_hw_timestamp(uint32_t channel, uint32_t flags) {
// 	return -1;
// }

// The case could be made that theres enough of a semantic difference to have irq_unmask and irq_mask
// on top of enable and disable

// tbd...
// static inline int sddf_gpio_irq_unmask(uint32_t channel) {
// 	return -1;
// }

// tbd...
// static inline int sddf_gpio_irq_mask(uint32_t channel) {
// 	return -1;
// }