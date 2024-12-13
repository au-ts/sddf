/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Implementation of the gpio driver targeting the ODROID C4.
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
uintptr_t gpio_regs;
uintptr_t gpio_ao_regs;
uintptr_t interupt_control_regs;

/* Channel Mappings (for O(1) notifying of forwardings IRQs from driver to client) */
/* (meson_channel - MESON_GPIO_IRQ_CHANNEL_START) to index into array */
int driver_to_client_channel_mappings[MESON_GPIO_IRQ_CHANNEL_COUNT] = {-1};

static void print_reg(uint32_t value) {
    char buffer[40];
    int pos = 0;

    for (int i = 31; i >= 0; i--) {
        uint32_t bit = (value >> i) & 1U;
        buffer[pos++] = bit ? '1' : '0';

        if (i % 8 == 0 && i != 0) {
            buffer[pos++] = ' ';
        }
    }

    // Add a newline at the end
    buffer[pos++] = '\n';

    // Null-terminate the string
    buffer[pos] = '\0';

    // Print the entire string in one go
    LOG_DRIVER("%s", buffer);
}

/* Notifications should only come from device */
void notified(microkit_channel ch)
{
    LOG_DRIVER("Driver Notified %d!\n", ch);
    switch (ch) {
        case GPIO_IRQ_0:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_1:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_2:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_3:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_4:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_5:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_6:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_IRQ_7:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_AO_IRQ_0:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        case GPIO_AO_IRQ_1:
            microkit_irq_ack(ch);
            microkit_notify(driver_to_client_channel_mappings[ch - MESON_GPIO_IRQ_CHANNEL_START]);
            break;
        default:
            LOG_DRIVER_ERR("Unexpected notification from %d!\n", ch);
    }
}

static meson_gpio_bank_t meson_get_gpio_bank(size_t pin) {
    if (pin < GPIO_Z) return GPIO_AO;
    if (pin < GPIO_H) return GPIO_Z;
    if (pin < BOOT) return GPIO_H;
    if (pin < GPIO_C) return BOOT;
    if (pin < GPIO_A) return GPIO_C;
    if (pin < GPIO_X) return GPIO_A;
    if (pin < GPIO_E) return GPIO_X;
    if (pin < TEST_N) return GPIO_E;
    if (pin < GPIO_ERROR_INVALID_PIN) return TEST_N;
    return GPIO_ERROR_INVALID_PIN;
}

// true if success | false if fail
static bool meson_irq_calc_reg_and_bits(meson_irq_reg_type_t function, size_t channel, uint32_t *reg_offset, uint32_t *start_bit) {
    // check if channel is too high
    if (channel < MESON_GPIO_IRQ_CHANNEL_START || channel >= MESON_GPIO_IRQ_CHANNEL_START + MESON_GPIO_IRQ_CHANNEL_COUNT) {
        return false;
    }

    // find function
    for (int i = 0; i < MESON_IRQ_FUNC_COUNT; i++) {
        if (irq_config_control[i].function == function) {

            // find reg and bits
            bool is_last = false;
            int k = 0;
            uint32_t bit_stride = meson_irq_bit_strides[function];

            // there will always be at least one register
            while (!is_last) {
                struct meson_irq_register_data reg_data = irq_config_control[i].registers[k];
                is_last = reg_data.is_last;
                k++;

                // see if the pin is in this register range
                if ((uint32_t)channel < reg_data.start_channel_number) {
                    return false;
                }

                uint32_t range = reg_data.end_bit - reg_data.start_bit + 1;
                range /= bit_stride;
                if ((uint32_t)channel > reg_data.start_channel_number + range - 1) {
                    continue; // check next register
                }

                // its in this register so find what bits
                *reg_offset = reg_data.register_offset;
                *start_bit = reg_data.start_bit + ((uint32_t)channel - reg_data.start_channel_number /* get the amount of channels after start bit */) * bit_stride;
                return true;
            }
        }
    }
    return false;
}

static bool meson_gpio_calc_reg_and_bits(meson_gpio_reg_type_t function, size_t pin, uint32_t *reg_offset, uint32_t *start_bit) {
    // check if pin is too high
    meson_gpio_bank_t bank = meson_get_gpio_bank(pin);
    if (bank == GPIO_ERROR_INVALID_PIN) {
        return false;
    }

    // find function
    for (int i = 0; i < MESON_GPIO_FUNC_COUNT; i++) {
        if (gpio_config_control[i].function == function) {

            // find bank
            for (int j = 0; j < MESON_GPIO_BANK_COUNT; j++) {
                if (gpio_config_control[i].banks[j].bank == bank) {

                    // find reg and bits
                    bool is_last = false;
                    int k = 0;
                    uint32_t bit_stride = meson_gpio_bit_strides[function];

                    // there will always be at least one register
                    while (!is_last) {
                        struct meson_gpio_register_data reg_data = gpio_config_control[i].banks[j].registers[k];
                        is_last = reg_data.is_last;
                        k++;

                        uint32_t bank_pin_number = (uint32_t)(pin) - (uint32_t)bank;

                        // see if the pin is in this register range
                        if (bank_pin_number < reg_data.start_pin_number) {
                            return false;
                        }

                        uint32_t range = reg_data.end_bit - reg_data.start_bit + 1;
                        range /= bit_stride;
                        if (bank_pin_number > reg_data.start_pin_number + range - 1) {
                            continue; // check next register
                        }

                        // its in this register so find what bits
                        *reg_offset = reg_data.register_offset;
                        *start_bit = reg_data.start_bit + (bank_pin_number - reg_data.start_pin_number /* get the amount of pins after start bit */) * bit_stride;
                        return true;
                    }
                }
            }
            return false;
        }
    }
    return false;
}

static volatile uint32_t *get_gpio_base_address(size_t pin) {
    meson_gpio_bank_t bank = meson_get_gpio_bank(pin);

    if (bank == GPIO_AO) {
        return (volatile uint32_t *)(gpio_ao_regs + GPIO_AO_REGS_BASE_ADDRESS_OFFSET);
    } else {
        return (volatile uint32_t *)(gpio_regs + GPIO_REGS_BASE_ADDRESS_OFFSET);
    }
}

static void meson_get_gpio_output(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_OUT, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void meson_get_gpio_input(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_IN, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void meson_get_gpio_direction(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DIR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // get value
    uint32_t value = ((*final_reg_address >> start_bit) & BIT(0)) == 0 ? GPIO_DIRECTION_OUTPUT : GPIO_DIRECTION_INPUT;

    *label = GPIO_SUCCESS;
    *response = value;
}

static void meson_get_gpio_pull(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULLEN, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    if (value == 0) {
        *label = GPIO_SUCCESS;
        *response = GPIO_NO_PULL;
        return;
    }

    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULL, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    if (value == 0) {
        *response = GPIO_PULL_DOWN;
    } else {
       *response = GPIO_PULL_UP;
    }
}

static void meson_get_gpio_drive_strength(size_t pin, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DS, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT_MASK(0, meson_gpio_bit_strides[MESON_GPIO_REG_DS]);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void meson_set_gpio_output(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != 0 && value != 1) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_OUT, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    *final_reg_address |= (BIT(0) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static void meson_set_gpio_direction(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != GPIO_DIRECTION_OUTPUT && value != GPIO_DIRECTION_INPUT) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DIR, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    *final_reg_address |= (BIT(0) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static void meson_set_gpio_pull(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != GPIO_PULL_UP && value != GPIO_PULL_DOWN && value != GPIO_NO_PULL) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULLEN, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    if (value == GPIO_NO_PULL) {
        *label = GPIO_SUCCESS;
        // print_reg(*final_reg_address);
        // LOG_DRIVER("Start bit : %d, reg offset %lx \n", start_bit, reg_offset);
        return;
    }

    *final_reg_address |= BIT(start_bit); // set

    // need to change other register as well
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULL, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    if (value == GPIO_PULL_DOWN) {
        *final_reg_address &= ~BIT(start_bit); // clear
    } else {
        *final_reg_address |= BIT(start_bit); // set
    }

    *label = GPIO_SUCCESS;
}

static void meson_set_gpio_drive_strength(size_t pin, size_t value, size_t* label, size_t* response) {
    if (value != GPIO_DS_500UA && value != GPIO_DS_2500UA && value != GPIO_DS_3000UA && value != GPIO_DS_4000UA) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DS, pin, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *gpio_base_address = get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = ((void *)gpio_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT_MASK(start_bit, start_bit + meson_gpio_bit_strides[MESON_GPIO_REG_DS]); // clear
    *final_reg_address |= (BIT_MASK(0, 0 + meson_gpio_bit_strides[MESON_GPIO_REG_DS]) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static void meson_get_irq_pin(size_t channel, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;

    meson_irq_reg_type_t reg_type;
    if (channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) {
        reg_type = MESON_IRQ_REG_AOSEL;
    } else {
        reg_type = MESON_IRQ_REG_SEL;
    }

    if (!meson_irq_calc_reg_and_bits(reg_type, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[reg_type]);

    *label = GPIO_SUCCESS;
    *response = value;
}

static void meson_get_irq_edge(size_t channel, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_BOTHEDGEEN, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    if (value == 1) {
        *label = GPIO_SUCCESS;
        *response = GPIO_IRQ_BOTH_RISING_FALLING;
        return;
    }

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_EDGE, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // get value
    value = (*final_reg_address >> start_bit) & BIT(0);

    if (value == 0) {
        *label = GPIO_SUCCESS;
        *response = GPIO_IRQ_LEVEL;
        return;
    }

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_POL, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // get value
    value = (*final_reg_address >> start_bit) & BIT(0);

    *label = GPIO_SUCCESS;
    if (value == 1) {
        *response = GPIO_IRQ_FALLING;
    } else {
       *response = GPIO_IRQ_RISING;
    }
}

static void meson_get_irq_filter(size_t channel, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_FIL, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // get value
    uint32_t value = (*final_reg_address >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[MESON_IRQ_REG_FIL]);
    if ((channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) && value == 1) {
        *response = GPIO_IRQ_FILTER_2600NS;
    } else {
        *response = value;
    }

    *label = GPIO_SUCCESS;
}

static void meson_set_irq_pin(size_t channel, size_t value, size_t* label, size_t* response) {
    meson_irq_reg_type_t reg_type;
    if (channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) {
        meson_gpio_bank_t bank = meson_get_gpio_bank(value);
        if (bank != GPIO_AO) {
            *label = GPIO_FAILURE;
            *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
            return;
        }
        reg_type = MESON_IRQ_REG_AOSEL;
    } else {
        meson_gpio_bank_t bank = meson_get_gpio_bank(value);
        if (bank == GPIO_ERROR_INVALID_PIN || bank == TEST_N) {
            *label = GPIO_FAILURE;
            *response = GPIO_INVALID_PIN_CONFIG_ENTRY;
            return;
        }
        reg_type = MESON_IRQ_REG_SEL;
    }

    uint32_t reg_offset;
    uint32_t start_bit;

    if (!meson_irq_calc_reg_and_bits(reg_type, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT_MASK(start_bit, start_bit + meson_irq_bit_strides[reg_type]); // clear
    *final_reg_address |= (BIT_MASK(0, 0 + meson_irq_bit_strides[reg_type]) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static void meson_set_irq_edge(size_t channel, size_t value, size_t* label, size_t* response) {
    if (value != GPIO_IRQ_BOTH_RISING_FALLING && value != GPIO_IRQ_RISING && value != GPIO_IRQ_FALLING && value != GPIO_IRQ_LEVEL) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
        return;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address;

    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_BOTHEDGEEN, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    if (value == GPIO_IRQ_BOTH_RISING_FALLING) {
        *final_reg_address |= BIT(start_bit); // set
        *label = GPIO_SUCCESS;
        return;
    }

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_EDGE, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    if (value == GPIO_IRQ_LEVEL) {
        *label = GPIO_SUCCESS;
        return;
    }
    *final_reg_address |= BIT(start_bit); // set

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_POL, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    *label = GPIO_SUCCESS;

    // set value
    *final_reg_address &= ~BIT(start_bit); // clear
    if (value == GPIO_IRQ_RISING) {
        return;
    }
    *final_reg_address |= BIT(start_bit); // set
}

static void meson_set_irq_filter(size_t channel, size_t value, size_t* label, size_t* response) {
    uint32_t reg_offset;
    uint32_t start_bit;

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_FIL, channel, &reg_offset, &start_bit)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_CHANNEL_CONFIG_ENTRY;
        return;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address = ((void *)irq_base_address + reg_offset * 4);

    if (channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) {
        if (value == GPIO_IRQ_FILTER_2600NS) {
            *final_reg_address |= BIT(start_bit); // set
            *label = GPIO_SUCCESS;
            return;
        } else if (value == GPIO_IRQ_FILTER_0NS) {
            *final_reg_address &= ~BIT(start_bit); // clear
            *label = GPIO_SUCCESS;
            return;
        } else {
            *label = GPIO_FAILURE;
            *response = GPIO_INVALID_VALUE;
            return;
        }
    }

    if (!(value >= GPIO_IRQ_FILTER_0NS && value <= GPIO_IRQ_FILTER_2331NS)) {
        *label = GPIO_FAILURE;
        *response = GPIO_INVALID_VALUE;
    }

    *final_reg_address &= ~BIT_MASK(start_bit, start_bit + meson_irq_bit_strides[MESON_IRQ_REG_FIL]); // clear
    *final_reg_address |= (BIT_MASK(0, 0 + meson_irq_bit_strides[MESON_IRQ_REG_FIL]) & value) << start_bit; // set

    *label = GPIO_SUCCESS;
}

static seL4_MessageInfo_t handle_get_gpio_request(size_t pin, size_t config) {
    size_t label;
    size_t response;

    switch (config) {
        case GPIO_OUTPUT:
            meson_get_gpio_output(pin, &label, &response);
            break;
        case GPIO_INPUT:
            meson_get_gpio_input(pin, &label, &response);
            break;
        case GPIO_DIRECTION:
            meson_get_gpio_direction(pin, &label, &response);
            break;
        case GPIO_PULL:
            meson_get_gpio_pull(pin, &label, &response);
            break;
        case GPIO_DRIVE_STRENGTH:
            meson_get_gpio_drive_strength(pin, &label, &response);
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
            meson_set_gpio_output(pin, value, &label, &response);
            break;
        case GPIO_DIRECTION:
            meson_set_gpio_direction(pin, value, &label, &response);
            break;
        case GPIO_PULL:
            meson_set_gpio_pull(pin, value, &label, &response);
            break;
        case GPIO_DRIVE_STRENGTH:
            meson_set_gpio_drive_strength(pin, value, &label, &response);
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
            meson_get_irq_pin(channel, &label, &response);
            break;
        case GPIO_IRQ_EDGE:
            meson_get_irq_edge(channel, &label, &response);
            break;
        case GPIO_IRQ_FILTER:
            meson_get_irq_filter(channel, &label, &response);
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
        case GPIO_IRQ_EDGE:
            meson_set_irq_edge(channel, value, &label, &response);
            break;
        case GPIO_IRQ_FILTER:
            meson_set_irq_filter(channel, value, &label, &response);
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
    size_t config, pin, meson_channel, value;

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
            meson_channel = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];
            return handle_get_irq_request(meson_channel, config);

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
            meson_channel = gpio_channel_mappings[ch][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];
            value = microkit_mr_get(GPIO_REQ_VALUE_SLOT);
            return handle_set_irq_request(meson_channel, config, value);

        default:
            seL4_MessageInfo_t message = microkit_msginfo_new(GPIO_FAILURE, 1);
            microkit_mr_set(GPIO_RES_VALUE_SLOT, (size_t)GPIO_INVALID_LABEL);
            return message;
    }
}

void init(void)
{
    LOG_DRIVER("Driver Init!\n");

    /* Configure gpio channel mappings */
    for (int i = 0; i < 52; i++) {
        /* Check if channel has been configured */
        if (gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT] != -1) {
            int meson_channel = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_IRQ_CHANNEL_SLOT];

            /* Check if its a valid configuration */
            if (meson_channel >= MESON_GPIO_IRQ_CHANNEL_START && meson_channel < MESON_GPIO_IRQ_CHANNEL_START + MESON_GPIO_IRQ_CHANNEL_COUNT) {
                /* Configure with hardware */
                size_t label;
                size_t response;
                meson_set_irq_pin(meson_channel, gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT], &label, &response);
                if (label == GPIO_FAILURE) {
                    LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] with gpio_irq_error_t : %ld!\n", i, response);
                    while (1) {}
                }
                meson_get_irq_pin(meson_channel, &label, &response);
                if (label == GPIO_FAILURE) {
                    LOG_DRIVER_ERR("Failed to config gpio_channel_mappings[%d] with gpio_irq_error_t : %ld!\n", i, response);
                    while (1) {}
                }
                if (response != gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_GPIO_PIN_SLOT]) {
                    LOG_DRIVER_ERR("Pin was not configuured properly, response : %ld!\n", response);
                    while (1) {}
                }

                /* Assign channel to the gpio pin */
                driver_to_client_channel_mappings[meson_channel - MESON_GPIO_IRQ_CHANNEL_START] = gpio_channel_mappings[i][GPIO_CHANNEL_MAPPING_CLIENTS_CHANNEL_SLOT];

                /* ACK the IRQ so we can recieve further IRQs */
                microkit_irq_ack(meson_channel);
            }
        }
    }
}