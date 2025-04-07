/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Implementation of the gpio driver targeting the MAAXBOARD.
// Made by Tristan Clinton-Muehr

#include <microkit.h>
#include "driver.h"
#include "gpio_config.h"

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("GPIO DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("GPIO DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/* Hardware memory */
uintptr_t gpio1_regs; // both gpio and irq regs
uintptr_t gpio2_regs; // both gpio and irq regs
uintptr_t gpio3_regs; // both gpio and irq regs
uintptr_t gpio4_regs; // both gpio and irq regs
uintptr_t gpio5_regs; // both gpio and irq regs

/* Channel Mappings (for O(1) notifying of forwardings IRQs from driver to client) */
/* ONLY FOR SINGLE CHANNELS THOUGH */
/* (imx_irq - MESON_GPIO_IRQ_CHANNEL_START) to index into array */
int driver_to_client_channel_mappings_single_irq_line[IMX_GPIO_IRQ_AH_GPIO1_7 - IMX_GPIO_IRQ_AH_GPIO1_0] = {-1};

/* For combined irq line */
void notify_combined(microkit_channel ch) {
    /* see which channels have configured this as there irq channel */
    for (int i = 0; i < 62; i++) {
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_SLOT] == ch) {
            int gpio_pin = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];

            /* see if the ISR for this pin has been flipped */
            uint32_t reg_offset;
            uint32_t start_bit;

            if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_ISR, gpio_pin, &reg_offset, &start_bit)) {
                LOG_DRIVER_ERR("Something was not caught during initialisation!\n");
                while (1) {};
            }

            volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(gpio_pin);
            volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

            uint32_t value = (*final_reg_address >> start_bit) & BIT(0);
            if (value) { // its set
                /* forward to the client */
                microkit_notify(gpio_channel_mappings[GPIO_CHANNEL_MAPPING_CLIENTS_CHANNEL_SLOT]);

                /* clear the status flag by setting to 1 */
                *final_reg_address &= BIT(start_bit);
            }
        }
    }
}


/* Notifications should only come from device */
void notified(microkit_channel ch)
{
    LOG_DRIVER("Driver Notified %d!\n", ch);
    switch (ch) {
        case IMX_GPIO_IRQ_AH_GPIO1_7:
        case IMX_GPIO_IRQ_AH_GPIO1_6:
        case IMX_GPIO_IRQ_AH_GPIO1_5:
        case IMX_GPIO_IRQ_AH_GPIO1_4:
        case IMX_GPIO_IRQ_AH_GPIO1_3:
        case IMX_GPIO_IRQ_AH_GPIO1_2:
        case IMX_GPIO_IRQ_AH_GPIO1_1:
        case IMX_GPIO_IRQ_AH_GPIO1_0:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings_single_irq_line[ch - IMX_GPIO_IRQ_AH_GPIO1_0]);
            break;
        case IMX_GPIO_IRQ_GPIO1_0_15:
        case IMX_GPIO_IRQ_GPIO1_16_31:
        case IMX_GPIO_IRQ_GPIO2_0_15:
        case IMX_GPIO_IRQ_GPIO2_16_31:
        case IMX_GPIO_IRQ_GPIO3_0_15:
        case IMX_GPIO_IRQ_GPIO3_16_31:
        case IMX_GPIO_IRQ_GPIO4_0_15:
        case IMX_GPIO_IRQ_GPIO4_16_31:
        case IMX_GPIO_IRQ_GPIO5_0_15:
        case IMX_GPIO_IRQ_GPIO5_16_31:
            microkit_irq_ack(ch);
            notify_combined(ch);
            break;
        default:
            LOG_DRIVER_ERR("Unexpected notification from %d!\n", ch);
    }
}

static imx_gpio_bank_t imx_get_gpio_instance(size_t pin) {
    if (pin < IMX_GPIO_INSTANCE_GPIO_2) return IMX_GPIO_INSTANCE_GPIO_1;
    if (pin < IMX_GPIO_INSTANCE_GPIO_3) return IMX_GPIO_INSTANCE_GPIO_2;
    if (pin < IMX_GPIO_INSTANCE_GPIO_4) return IMX_GPIO_INSTANCE_GPIO_3;
    if (pin < IMX_GPIO_INSTANCE_GPIO_5) return IMX_GPIO_INSTANCE_GPIO_4;
    if (pin < IMX_GPIO_INVALID_PIN) return IMX_GPIO_INSTANCE_GPIO_5;
    return IMX_GPIO_INVALID_PIN;
}

static volatile uint32_t *imx_get_gpio_and_gpio_and_irq_base_address(size_t pin) {
    imx_gpio_instance_t instance = imx_get_gpio_instance(pin);

    if (instance == IMX_GPIO_INSTANCE_GPIO_1) return (volatile uint32_t *)(gpio1_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_2) return (volatile uint32_t *)(gpio2_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_3) return (volatile uint32_t *)(gpio3_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_4) return (volatile uint32_t *)(gpio4_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_5) return (volatile uint32_t *)(gpio5_regs + 0 /*base address offest due to page alignmemt*/);
}

static bool imx_is_valid_irq_config(int irq) {
    return (irq >= IMX_GPIO_IRQ_CHANNEL_START
        && irq < IMX_GPIO_IRQ_CHANNEL_START + IMX_GPIO_IRQ_CHANNEL_COUNT
        && gpio_channel_mappings[irq][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] == -1
        && gpio_channel_mappings[irq][GPIO_CHANNEL_MAPPING_IRQ_SLOT] == -1);
}

static bool imx_check_irq_is_combined(int irq) {
    return irq <= IMX_GPIO_IRQ_AH_GPIO1_7 && irq >= IMX_GPIO_IRQ_AH_GPIO1_0;
}

static int imx_get_irq_from_config_file(size_t pin) {
    for (int i = 0; i < 62; i++) {
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] == pin) {
            return gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_SLOT];
        }
    }
    return -1; // never happens
}

static bool imx_gpio_and_irq_calculate_reg_and_bits(imx_gpio_and_irq_reg_type_t function, size_t pin, uint32_t *reg_offset, uint32_t *start_bit) {
    // check if pin is too high
    imx_gpio_instance_t instance = imx_get_gpio_instance(pin);
    if (instance == IMX_GPIO_INVALID_PIN) {
        return false;
    }

    // find function
    for (int i = 0; i < IMX_GPIO_AND_IRQ_FUNC_COUNT; i++) {
        if (gpio_and_irq_config_control[i].function == function) {

            // find instance
            for (int j = 0; j < IMX_GPIO_INSTANCE_COUNT; j++) {
                if (gpio_and_irq_config_control[i].instances[j].instance == instance) {
                    // find reg and bits
                    bool is_last = false;
                    int k = 0;
                    uint32_t bit_stride = imx_gpio_and_irq_bit_strides[function];

                    // there will always be at least one register
                    while (!is_last) {
                        struct imx_gpio_and_irq_register_data reg_data = gpio_and_irq_config_control[i].instances[j].registers[k];
                        is_last = reg_data.is_last;
                        k++;

                        uint32_t instance_pin_number = (uint32_t)(pin) - (uint32_t)instance;

                        // see if the pin is in this register range
                        if (instance_pin_number < reg_data.start_pin_number) {
                            // we missed it
                            return false;
                        }

                        uint32_t range = 32;
                        range /= bit_stride;
                        if (instance_pin_number > reg_data.start_pin_number + range - 1) {
                            continue; // check next register
                        }

                        // its in this register so find what bits
                        *reg_offset = reg_data.register_offset;
                        *start_bit = (instance_pin_number - reg_data.start_pin_number /* get the amount of pins after start bit */) * bit_stride;
                        return true;
                    }
                }
            }
        }
    }
    return true; // never get here
}

/* GETS | GPIO */

static void imx_get_gpio_output(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_GPIO_REG_DR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_PIN_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void imx_get_gpio_input(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_GPIO_REG_PSR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_PIN_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void imx_get_gpio_direction(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_GPIO_REG_GDIR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_PIN_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // get value
    uint32_t value = ((*final_reg_address >> start_bit) & BIT(0)) == 1 ? GPIO_DIRECTION_OUTPUT : GPIO_DIRECTION_INPUT;

    *label = GPIO_SUCCESS;
    *response = value;
}

/* GETS | IRQ */

/* All this does is check if the IMR is set for this pin and if so returns the pin back */
static void imx_get_irq_pin(size_t pin, size_t* label, size_t* response) {
    /* check if its combined (the only ones that can be configured in registers) */
    if (!imx_check_irq_is_combined(imx_get_irq_from_config_file(pin))) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
    }

    /* Check IMR reg */
    uint32_t reg_offset;
    uint32_t start_bit;

    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_REG_IMR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_PIN_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(value);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);
    if (value) { // its set
        /* then we return the pin in the response */
        *label = GPIO_SUCCESS;
        *response = pin;
    } else {
        /* we return the error pin in the response because its equivalent to not being set */
        *label = GPIO_FAILURE;
        *response = IMX_GPIO_INVALID_PIN;
    }
}

static void imx_get_irq_edge(size_t pin, size_t* label, size_t* response) {
    /* check if its combined (the only ones that can be configured in registers) */
    if (!imx_check_irq_is_combined(imx_get_irq_from_config_file(pin))) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
    }

    uint32_t reg_offset;
    uint32_t start_bit;

    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_EDGE_SEL, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(value);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    if (value == 1) {
        *label = GPIO_SUCCESS;
        *response = IMX_GPIO_IRQ_ANY_EDGE;
        return;
    }

    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_ICR, irq, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
        return;
    }

    final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    value = (*final_reg_address >> start_bit) & BIT_MASK(0, imx_gpio_and_irq_bit_strides[IMX_IRQ_ICR]);

    *label = GPIO_SUCCESS;
    if (value == 0) {
        *response = IMX_GPIO_IRQ_LOW_LEVEL;
    } else if (value == 1) {
        *response = IMX_GPIO_IRQ_HIGH_LEVEL;
    } else if (value == 2) {
        *response = IMX_GPIO_IRQ_RISING_EDGE;
    } else {
        *response = IMX_GPIO_IRQ_FALLING_EDGE;
    }
}

/* SETS | GPIO */

static void imx_set_gpio_output(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != 0 && value != 1) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_GPIO_REG_DR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_PIN_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    *final_reg_address |= (BIT(0) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static void imx_set_gpio_direction(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != GPIO_DIRECTION_OUTPUT && value != GPIO_DIRECTION_INPUT) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_GPIO_REG_GDIR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_PIN_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // set value
    if (value == GPIO_DIRECTION_INPUT) {
        *final_reg_address &= ~BIT(start_bit); // clear
    } else {
        *final_reg_address |= BIT(start_bit); // set
    }

    *label = GPIO_SUCCESS;
}

/* SETS | IRQ */

static void imx_set_irq_pin(size_t pin, size_t value, size_t* label, size_t* response) {
    /* check if the irq is a combined irq */
    if (imx_check_irq_is_combined(value)) {
        /* check if this value (pin) can be configured to this channel */
        if (pin == value - IMX_GPIO_IRQ_CHANNEL_START) {
            *label = GPIO_FAILURE;
            *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
            return;
        } else {
            /* no configuration is neccessary */
            *label = GPIO_SUCCESS;
            return;
        }
    }

    /* handling of the combined channels that requires actually interacting with hardware register */
    size_t start_valid_pin = 16 * (value - IMX_GPIO_IRQ_GPIO1_0_15);
    size_t end_valid_pin = start_valid_pin + 15;
    if (pin < start_valid_pin || pin > end_valid_pin) {
        /* this pin cannot be configured for this combined interrupt */
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
        return;
    }

    /* set the mask so pin configures interrupts */

    uint32_t reg_offset;
    uint32_t start_bit;

    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_REG_IMR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(value);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // set value
    *final_reg_address |= BIT(start_bit); // set

    *label = GPIO_SUCCESS;
}

static void imx_set_irq_edge(size_t pin, size_t value, size_t* label, size_t* response) {
    /* check if its combined (the only ones that can be configured in registers) */
    if (!imx_check_irq_is_combined(imx_get_irq_from_config_file(pin))) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
    }

    if (value != IMX_GPIO_IRQ_LOW_LEVEL &&
        value != IMX_GPIO_IRQ_HIGH_LEVEL &&
        value != IMX_GPIO_IRQ_RISING_EDGE &&
        value != IMX_GPIO_IRQ_FALLING_EDGE &&
        value != IMX_GPIO_IRQ_ANY_EDGE)
    {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;

    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_EDGE_SEL, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
        return;
    }

    volatile uint32_t *gpio_and_irq_base_address = imx_get_gpio_and_gpio_and_irq_base_address(value);
    volatile uint32_t *final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    if (value == IMX_GPIO_IRQ_ANY_EDGE) {
        *final_reg_address |= BIT(start_bit); // set
        *label = GPIO_SUCCESS;
        return;
    }

    if (!imx_gpio_and_irq_calculate_reg_and_bits(IMX_IRQ_ICR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG;
        return;
    }

    final_reg_address = ((void *)gpio_and_irq_base_address + reg_offset);

    // set value
    *final_reg_address &= ~BIT_MASK(start_bit, start_bit + imx_gpio_and_irq_bit_strides[IMX_IRQ_ICR]); // clear
    *final_reg_address |= (BIT_MASK(0, 0 + imx_gpio_and_irq_bit_strides[IMX_IRQ_ICR]) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

/* HANDLERS */

static seL4_MessageInfo_t handle_get_gpio_request(size_t pin, size_t config) {
    size_t label;
    size_t response;

    switch (config) {
        case GPIO_OUTPUT:
            imx_get_gpio_output(pin, &label, &response);
            break;
        case GPIO_INPUT:
            imx_get_gpio_input(pin, &label, &response);
            break;
        case GPIO_DIRECTION:
            imx_get_gpio_direction(pin, &label, &response);
            break;
        default:
            label = GPIO_FAILURE;
            response = GPIO_ERROR_INVALID_CONFIG;
    }

    seL4_MessageInfo_t message = microkit_msginfo_new(label, 1);
    microkit_mr_set(GPIO_RES_VALUE_SLOT, response);
    return message;
}

static seL4_MessageInfo_t handle_set_gpio_request(size_t pin, size_t config, size_t value) {
    size_t label;
    size_t response;

    switch (config) {
        case GPIO_OUTPUT:
            imx_set_gpio_output(pin, value, &label, &response);
            break;
        case GPIO_DIRECTION:
            imx_set_gpio_direction(pin, value, &label, &response);
            break;
        default:
            label = GPIO_FAILURE;
            response = GPIO_ERROR_INVALID_CONFIG;
    }

    seL4_MessageInfo_t message;
    if (label == GPIO_FAILURE) {
        message = microkit_msginfo_new(label, 1);
        microkit_mr_set(GPIO_RES_VALUE_SLOT, response);
    } else {
        message = microkit_msginfo_new(label, 0);
    }

    return message;
}

static seL4_MessageInfo_t handle_get_irq_request(size_t pin, size_t config) {
    size_t label;
    size_t response;

    switch (config) {
        case GPIO_IRQ_PIN:
            imx_get_irq_pin(pin, &label, &response);
            break;
        case IMX_GPIO_IRQ_EDGE:
            imx_get_irq_edge(pin, &label, &response);
            break;
        default:
            label = GPIO_FAILURE;
            response = GPIO_ERROR_INVALID_CONFIG;
    }

    seL4_MessageInfo_t message = microkit_msginfo_new(label, 1);
    microkit_mr_set(GPIO_RES_VALUE_SLOT, response);
    return message;
}

static seL4_MessageInfo_t handle_set_irq_request(size_t pin, size_t config, size_t value) {
    size_t label;
    size_t response;

    switch (config) {
        case IMX_GPIO_IRQ_EDGE:
            imx_set_irq_edge(pin, value, &label, &response);
            break;
        default:
            label = GPIO_FAILURE;
            response = GPIO_ERROR_INVALID_CONFIG;
    }

    seL4_MessageInfo_t message;
    if (label == GPIO_FAILURE) {
        message = microkit_msginfo_new(label, 1);
        microkit_mr_set(GPIO_RES_VALUE_SLOT, response);
    } else {
        message = microkit_msginfo_new(label, 0);
    }

    return message;
}

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t count = microkit_msginfo_get_count(msginfo);
    size_t config, pin, value;

    switch (label) {
        case GPIO_GET_GPIO:
            if (count != 1) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_INVALID_NUM_ARGS);
                return message;
            }

            /* Check GPIO mapping permissions */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_PERMISSION_DENIED);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            pin = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];

            return handle_get_gpio_request(pin, config);

        case GPIO_GET_IRQ:
            if (count != 1) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_INVALID_NUM_ARGS);
                return message;
            }

            /* Check irq channel mapping permissions */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_PERMISSION_DENIED);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            pin = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];

            return handle_get_irq_request(pin, config);

        case GPIO_SET_GPIO:
            if (count != 2) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_INVALID_NUM_ARGS);
                return message;
            }

            /* Check GPIO mapping permissions */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_PERMISSION_DENIED);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            pin = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];
            value = microkit_mr_get(GPIO_REQ_VALUE_SLOT);

            return handle_set_gpio_request(pin, config, value);

        case GPIO_SET_IRQ:
            if (count != 2) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_INVALID_NUM_ARGS);
                return message;
            }

            /* Check irq channel mapping permissions */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_PERMISSION_DENIED);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            pin = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];
            value = microkit_mr_get(GPIO_REQ_VALUE_SLOT);

            return handle_set_irq_request(pin, config, value);

        default:
            seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
            microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_ERROR_INVALID_LABEL);
            return message;
    }

}

void init(void)
{
    LOG_DRIVER("Driver Init!\n");

    /* Configure gpio channel mappings */
    for (int i = 0; i < 62; i++) {
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] == -1 && gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_SLOT] != -1) {
            LOG_DRIVER_ERR("GPIO pin must be set if IRQ is set!\n");
            while (1) {}
        } else if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] == -1) {
            continue;
        }

        int gpio_pin = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];

        /* If GPIO pin is configured make sure its only configured to a client channel once */
        int count = 0;
        for (int j = 0; j < 62; j++) {
            if (gpio_pin == gpio_channel_mappings[j][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT]) {
                count++;
            }
        }

        if (count != 1) {
            LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] because GPIO pin is not configured ONLY ONCE\n", i, response);
            while (1) {}
        }

        /* Check if IRQ has been configured for this GPIO */
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_SLOT] != -1) {
            int irq = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_SLOT];

            /* Check if its a valid irq configuration (its in range + corresponding device channel entry in table is uninitialised) */
            if (!imx_is_valid_irq_config(irq)) {
                LOG_DRIVER_ERR("Failed to config irq!\n");
                while (1) {}
            }

            /* Configure with hardware */
            size_t label;
            size_t response;
            imx_set_irq_pin(gpio_pin, irq, &label, &response);
            if (label == GPIO_FAILURE) {
                LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] with gpio_irq_error_t : %ld!\n", i, response);
                while (1) {}
            }
            /* Since imx_get_irq_pin is just checking the IMR register we dont need to worry if it fails because its unsupported (irq was NOT COMBINED)*/
            imx_get_irq_pin(gpio_pin, &label, &response);
            if (label == GPIO_FAILURE && (response != GPIO_ERROR_UNSUPPORTED_IRQ_CONFIG)) {
                LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] with gpio_irq_error_t : %ld!\n", i, response);
                while (1) {}
            }

            /* Assign single channel to the gpio pin */
            if (imx_check_irq_is_combined(irq)) {
                driver_to_client_channel_mappings_single_irq_line[irq - IMX_GPIO_IRQ_AH_GPIO1_0] = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_CLIENTS_CHANNEL_SLOT];
            }

            /* ACK the IRQ so we can recieve further IRQs */
            microkit_irq_ack(irq);
        }
    }
}