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

/* Notifications should only come from device */
/* TODO: */
void notified(microkit_channel ch)
{
    LOG_DRIVER("Driver Notified %d!\n", ch);
    switch (ch) {
        case IMX_GPIO_IRQ_AH_GPIO1_7:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_6:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_5:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_4:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_3:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_2:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_1:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_AH_GPIO1_0:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO1_0_15:
            // TODO: find the channels that set off the INT
            notify_active_interupts_on_combined_interrupt_line(ch);
            microkit_irq_ack(ch);
            break;
        case IMX_GPIO_IRQ_GPIO1_16_31:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO2_0_15:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO2_16_31:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO3_0_15:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO3_16_31:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO4_0_15:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO4_16_31:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO5_0_15:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
            break;
        case IMX_GPIO_IRQ_GPIO5_16_31:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - IMX_GPIO_IRQ_CHANNEL_START]);
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
    if (pin < IMX_GPIO_ERROR_INVALID_PIN) return IMX_GPIO_INSTANCE_GPIO_5;
    return IMX_GPIO_ERROR_INVALID_PIN;
}

static volatile uint32_t *get_gpio_and_irq_base_address(size_t pin) {
    imx_gpio_instance_t instance = imx_get_gpio_instance(pin);

    if (instance == IMX_GPIO_INSTANCE_GPIO_1) return (volatile uint32_t *)(gpio1_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_2) return (volatile uint32_t *)(gpio2_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_3) return (volatile uint32_t *)(gpio3_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_4) return (volatile uint32_t *)(gpio4_regs + 0 /*base address offest due to page alignmemt*/);
    if (instance == IMX_GPIO_INSTANCE_GPIO_5) return (volatile uint32_t *)(gpio5_regs + 0 /*base address offest due to page alignmemt*/);
}

static bool imx_gpio_calc_reg_and_bits(imx_gpio_reg_type_t function, size_t pin, uint32_t *reg_offset, uint32_t *start_bit) {
    // check if pin is too high
    imx_gpio_instance_t instance = imx_get_gpio_instance(pin);
    if (instance == IMX_GPIO_ERROR_INVALID_PIN) {
        return false;
    }

    // find function
    for (int i = 0; i < IMX_GPIO_FUNC_COUNT; i++) {
        if (gpio_config_control[i].function == function) {

            // find instance
            for (int j = 0; j < IMX_GPIO_INSTANCE_COUNT; j++) {
                if (gpio_config_control[i].instances[j].instance == instance) {

                    // find reg and bits
                    *reg_offset = gpio_config_control[i].instances[j].register_offset;
                    *start_bit = (uint32_t)pin - (uint32_t)instance;
                }
            }
        }
    }
    return true;
}

static bool imx_irq_calc_reg_and_bits(imx_irq_reg_type_t function, size_t pin, uint32_t *reg_offset, uint32_t *start_bit) {
    // check if pin is too high
    imx_gpio_instance_t instance = imx_get_gpio_instance(pin);
    if (instance == IMX_GPIO_ERROR_INVALID_PIN) {
        return false;
    }

    // find function
    for (int i = 0; i < IMX_IRQ_FUNC_COUNT; i++) {
        if (irq_config_control[i].function == function) {

            // find instance
            for (int j = 0; j < IMX_GPIO_INSTANCE_COUNT; j++) {
                if (irq_config_control[i].instances[j].instance == instance) {

                    // find reg and bits
                    *reg_offset = irq_config_control[i].instances[j].register_offset;
                    *start_bit = (uint32_t)pin - (uint32_t)instance;
                }
            }
        }
    }
    return true;
}

/* GETS */

static void imx_get_gpio_output(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_calc_reg_and_bits(IMX_GPIO_REG_DR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void imx_get_gpio_input(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_calc_reg_and_bits(IMX_GPIO_REG_PSR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void imx_get_gpio_direction(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_calc_reg_and_bits(IMX_GPIO_REG_GDIR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset);

    // get value
    uint32_t value = ((*final_reg_address >> start_bit) & BIT(0)) == 1 ? GPIO_DIRECTION_OUTPUT : GPIO_DIRECTION_INPUT;

    *label = GPIO_SUCCESS;
    *response = value;
}

static void imx_get_interrupt_channel_from_client_channel(size_t channel) {
    int imx_device_channel = gpio_channel_mappings[channel][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];

}

static void imx_get_irq_pin(size_t channel, size_t* label, size_t* response) {
    // dont use the config file actually check in the registers as this is more useful
    // you could just check the ocnfig file as the client anyway if you wanted

    // since we can have combined GPIO for a channel,
        // we need to check which one is configured to channel
        // the only way to do that is through the config file
        // OR we can useanother data structure
        // i think using the config file is best because its only not used in emson because combinations dont exist
        // so we could just hceck the register
        // in this case theres literally no way to know
        // i guess we should use BOTH the register and the config file to just double check



    // so we have the clients channel so check which INT and pin its for
    // now go and check the hardware is set to that

    // probably need a function for this because it will get resued in the notified entry point
    // int imx_device_channel = gpio_channel_mappings[channel][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];
    int gpio_pin = gpio_channel_mappings[channel][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];

    // check that this bit is set in the IMR register

    
    
    // uint32_t reg_offset;
    // uint32_t start_bit;

    // meson_irq_reg_type_t reg_type;
    // if (channel ==  MESON_GPIO_AO_IRQ_0 || channel == MESON_GPIO_AO_IRQ_1) {
    //     reg_type = MESON_IRQ_REG_AOSEL;
    // } else {
    //     reg_type = MESON_IRQ_REG_SEL;
    // }

    // if (!meson_irq_calc_reg_and_bits(reg_type, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    // volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // // get value
    // uint32_t value = (*final_reg_address >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[reg_type]);

    // *label = GPIO_SUCCESS;
    // *response = value;
}

// TODO:
static void imx_get_irq_edge(size_t channel, size_t* label, size_t* response) {
    // uint32_t reg_offset;
    // uint32_t start_bit;
    // if (!imx_irq_calc_reg_and_bits(IMX_GPIO_IRQ_EDGE, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // // TODO: we must look up the pin based on the channel (this will be in the channel mappings)

    // volatile uint32_t *irq_base_address = get_gpio_and_irq_base_address(pin);
    // volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset);

    // // get value
    // uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    // if (value == 1) {
    //     *label = GPIO_SUCCESS;
    //     *response = MESON_GPIO_IRQ_BOTH_RISING_FALLING;
    //     return;
    // }

    // if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_EDGE, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // // get value
    // value = (*final_reg_address >> start_bit) & BIT(0);

    // if (value == 0) {
    //     *label = GPIO_SUCCESS;
    //     *response = MESON_GPIO_IRQ_LEVEL;
    //     return;
    // }

    // if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_POL, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // // get value
    // value = (*final_reg_address >> start_bit) & BIT(0);

    // *label = GPIO_SUCCESS;
    // if (value == 1) {
    //     *response = MESON_GPIO_IRQ_FALLING;
    // } else {
    //    *response = MESON_GPIO_IRQ_RISING;
    // }
}

/* SETS */

static void imx_set_gpio_output(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != 0 && value != 1) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_calc_reg_and_bits(IMX_GPIO_REG_DR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    *final_reg_address |= (BIT(0) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static void imx_set_gpio_direction(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != GPIO_DIRECTION_OUTPUT && value != GPIO_DIRECTION_INPUT) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!imx_gpio_calc_reg_and_bits(IMX_GPIO_REG_GDIR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_and_irq_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset);

    // set value
    if (value == GPIO_DIRECTION_INPUT) {
        *final_reg_address &= ~BIT(start_bit); // clear
    } else {
        *final_reg_address |= BIT(start_bit); // set
    }

    *label = GPIO_SUCCESS;
}

static void imx_set_irq_pin(size_t channel, size_t value, size_t* label, size_t* response) {
    /* check if the value is a combined channel */
    if (channel >= IMX_GPIO_IRQ_AH_GPIO1_7 && channel <= IMX_GPIO_IRQ_AH_GPIO1_0) {
        /* check if this value (pin) can be configured to this channel */
        if (value == channel - IMX_GPIO_IRQ_CHANNEL_START) {
            *label = GPIO_FAILURE;
            *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
            return;
        } else {
            /* no configuration is neccessary */
            *label = GPIO_SUCCESS;
            return;
        }
    }

    /* handling of the combined channels */

    size_t start_valid_pin = 16 * (channel - IMX_GPIO_IRQ_GPIO1_0_15);
    size_t end_valid_pin = start_valid_pin + 15;
    if (value < start_valid_pin || value > end_valid_pin) {
        /* pin cannot be configured for this combined interrupt */
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    /* set the mask so pin configures interrupts */

    uint32_t reg_offset;
    uint32_t start_bit;

    if (!imx_irq_calc_reg_and_bits(IMX_IRQ_REG_IMR, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *irq_base_address = get_gpio_and_irq_base_address(value);
    volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset);

    // set value
    if (value == GPIO_DIRECTION_INPUT) {
        *final_reg_address &= ~BIT(start_bit); // clear
    } else {
        *final_reg_address |= BIT(start_bit); // set
    }

    *label = GPIO_SUCCESS;
}

// TODO:
static void imx_set_irq_edge(size_t channel, size_t value, size_t* label, size_t* response) {
    // if (value != MESON_GPIO_IRQ_BOTH_RISING_FALLING && value != MESON_GPIO_IRQ_RISING && value != MESON_GPIO_IRQ_FALLING && value != MESON_GPIO_IRQ_LEVEL) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_VALUE;
    //     return;
    // }

    // volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    // volatile uint32_t *final_reg_address;

    // uint32_t reg_offset;
    // uint32_t start_bit;
    // if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_BOTHEDGEEN, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // // set value
    // *final_reg_address &= ~BIT(start_bit); // clear
    // if (value == MESON_GPIO_IRQ_BOTH_RISING_FALLING) {
    //     *final_reg_address |= BIT(start_bit); // set
    //     *label = GPIO_SUCCESS;
    //     return;
    // }

    // if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_EDGE, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // // set value
    // *final_reg_address &= ~BIT(start_bit); // clear
    // if (value == MESON_GPIO_IRQ_LEVEL) {
    //     *label = GPIO_SUCCESS;
    //     return;
    // }
    // *final_reg_address |= BIT(start_bit); // set

    // if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_POL, channel, &reg_offset, &start_bit)) {
    //     *label = GPIO_FAILURE;
    //     *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
    //     return;
    // }

    // final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // *label = GPIO_SUCCESS;

    // // set value
    // *final_reg_address &= ~BIT(start_bit); // clear
    // if (value == MESON_GPIO_IRQ_RISING) {
    //     return;
    // }
    // *final_reg_address |= BIT(start_bit); // set
}

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
            response = GPIO_INVALID_CONFIG;
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
            response = GPIO_INVALID_CONFIG;
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

static seL4_MessageInfo_t handle_get_irq_request(size_t channel, size_t config) {
    size_t label;
    size_t response;

    switch (config) {
        case GPIO_IRQ_PIN:
            imx_get_irq_pin(channel, &label, &response);
            break;
        case IMX_GPIO_IRQ_EDGE:
            imx_get_irq_edge(channel, &label, &response);
            break;
        default:
            label = GPIO_FAILURE;
            response = GPIO_INVALID_CONFIG;
    }

    seL4_MessageInfo_t message = microkit_msginfo_new(label, 1);
    microkit_mr_set(GPIO_RES_VALUE_SLOT, response);
    return message;
}

static seL4_MessageInfo_t handle_set_irq_request(size_t channel, size_t config, size_t value) {
    size_t label;
    size_t response;

    switch (config) {
        case IMX_GPIO_IRQ_EDGE:
            imx_set_irq_edge(channel, value, &label, &response);
            break;
        default:
            label = GPIO_FAILURE;
            response = GPIO_INVALID_CONFIG;
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
    size_t config, pin, imx_channel, value;

    switch (label) {
        case GPIO_GET_GPIO:
            if (count != 1) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_NUM_ARGS);
                return message;
            }

            /* Check GPIO mapping */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_MAPPING_ENTRY);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            pin = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];
            return handle_get_gpio_request(pin, config);

        case GPIO_GET_IRQ:
            if (count != 1) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_NUM_ARGS);
                return message;
            }

            /* Check irq channel mapping */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_MAPPING_ENTRY);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            imx_channel = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];
            return handle_get_irq_request(imx_channel, config);


        case GPIO_SET_GPIO:
            if (count != 2) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_NUM_ARGS);
                return message;
            }

            /* Check GPIO mapping */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_MAPPING_ENTRY);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            pin = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT];
            value = microkit_mr_get(GPIO_REQ_VALUE_SLOT);
            return handle_set_gpio_request(pin, config, value);

        case GPIO_SET_IRQ:
            if (count != 2) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_NUM_ARGS);
                return message;
            }

            /* Check irq channel mapping */
            if (gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT] < 0) {
                seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
                microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_MAPPING_ENTRY);
                return message;
            }

            config = microkit_mr_get(GPIO_REQ_CONFIG_SLOT);
            imx_channel = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];
            value = microkit_mr_get(GPIO_REQ_VALUE_SLOT);
            return handle_set_irq_request(imx_channel, config, value);


        default:
            seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
            microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_LABEL);
            return message;
    }

}

static bool imx_is_valid_irq_config(int imx_device_channel) {
    return (imx_device_channel >= IMX_GPIO_IRQ_CHANNEL_START
        && imx_device_channel < IMX_GPIO_IRQ_CHANNEL_START + IMX_GPIO_IRQ_CHANNEL_COUNT
        && gpio_channel_mappings[imx_device_channel][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] == -1
        && gpio_channel_mappings[imx_device_channel][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT] == -1);
}

void init(void)
{
    LOG_DRIVER("Driver Init!\n");

    /* Configure gpio channel mappings */
    for (int i = 0; i < 62; i++) {
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT] == -1) {
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
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT] != -1) {
            int imx_device_channel = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];

            /* Check if its a valid irq configuration (its in range + corresponding device channel entry in table is uninitialised) */
            if (!imx_is_valid_irq_config(imx_device_channel)) {
                LOG_DRIVER_ERR("Failed to config irq imx_device_channel!\n");
                while (1) {}
            }

            /* Configure with hardware */
            size_t label;
            size_t response;
            imx_set_irq_pin(imx_device_channel, gpio_pin, &label, &response);
            if (label == GPIO_FAILURE) {
                LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] with gpio_irq_error_t : %ld!\n", i, response);
                while (1) {}
            }
            imx_get_irq_pin(imx_device_channel, &label, &response);
            if (label == GPIO_FAILURE) {
                LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] with gpio_irq_error_t : %ld!\n", i, response);
                while (1) {}
            }
            if (response != gpio_pin) {
                LOG_DRIVER_ERR("Pin was not configuured properly, response : %ld!\n", response);
                while (1) {}
            }

            /* ACK the IRQ so we can recieve further IRQs */
            microkit_irq_ack(imx_device_channel);
        }
    }
}