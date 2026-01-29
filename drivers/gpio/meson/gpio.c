/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Implementation of the gpio driver targeting the ODROID C4.
// Made by Tristan Clinton-Muehr

#include <microkit.h>
#include <sddf/gpio/protocol.h>
#include "driver.h"
#include "gpio_config.h"

// #define DEBUG_DRIVER

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
/* (meson_irq - MESON_GPIO_IRQ_CHANNEL_START) to index into array */
int driver_to_client_channel_mappings[MESON_GPIO_IRQ_CHANNEL_COUNT] = {-1};

/* Track IRQ enabled state per channel */
static bool irq_enabled[MESON_GPIO_IRQ_CHANNEL_COUNT] = {false};

static void print_reg(uint32_t value)
{
    char buffer[40];
    int pos = 0;

    for (int i = 31; i >= 0; i--) {
        uint32_t bit = (value >> i) & 1U;
        buffer[pos++] = bit ? '1' : '0';

        if (i % 8 == 0 && i != 0) {
            buffer[pos++] = ' ';
        }
    }

    buffer[pos++] = '\n';
    buffer[pos] = '\0';

    LOG_DRIVER("%s", buffer);
}

static inline seL4_MessageInfo_t error_response(gpio_error_t error_code)
{
    uint32_t e = error_code | BIT(SDDF_GPIO_RESPONSE_ERROR_BIT);
    return microkit_msginfo_new(e, 0);
}

static inline bool check_irq_permission(microkit_channel ch)
{
    return gpio_driver_channel_mappings[ch].irq >= 0;
}

/* Notifications should only come from device */
void notified(microkit_channel ch)
{
    LOG_DRIVER("Driver Notified %d!\n", ch);
    switch (ch) {
        case MESON_GPIO_IRQ_0:
        case MESON_GPIO_IRQ_1:
        case MESON_GPIO_IRQ_2:
        case MESON_GPIO_IRQ_3:
        case MESON_GPIO_IRQ_4:
        case MESON_GPIO_IRQ_5:
        case MESON_GPIO_IRQ_6:
        case MESON_GPIO_IRQ_7:
        case MESON_GPIO_AO_IRQ_0:
        case MESON_GPIO_AO_IRQ_1: {
            int irq_idx = ch - MESON_GPIO_IRQ_CHANNEL_START;
            if (irq_enabled[irq_idx]) {
                irq_enabled[irq_idx] = false;
                microkit_irq_ack(ch);
                microkit_notify(driver_to_client_channel_mappings[irq_idx]);
            } else {
                microkit_irq_ack(ch);
            }
            break;
        }
        default:
            LOG_DRIVER_ERR("Unexpected notification from %d!\n", ch);
    }
}

static meson_gpio_bank_t meson_get_gpio_bank(size_t pin)
{
    if (pin < MESON_GPIO_Z) return MESON_GPIO_AO;
    if (pin < MESON_GPIO_H) return MESON_GPIO_Z;
    if (pin < MESON_GPIO_BOOT) return MESON_GPIO_H;
    if (pin < MESON_GPIO_C) return MESON_GPIO_BOOT;
    if (pin < MESON_GPIO_A) return MESON_GPIO_C;
    if (pin < MESON_GPIO_X) return MESON_GPIO_A;
    if (pin < MESON_GPIO_E) return MESON_GPIO_X;
    if (pin < MESON_GPIO_TEST_N) return MESON_GPIO_E;
    if (pin < MESON_GPIO_ERROR_INVALID_PIN) return MESON_GPIO_TEST_N;
    return MESON_GPIO_ERROR_INVALID_PIN;
}

static bool meson_is_valid_irq_config(int irq)
{
    return (irq >= MESON_GPIO_IRQ_CHANNEL_START
        && irq < MESON_GPIO_IRQ_CHANNEL_START + MESON_GPIO_IRQ_CHANNEL_COUNT
        && gpio_driver_channel_mappings[irq].pin == -1
        && gpio_driver_channel_mappings[irq].irq == -1);
}

/* true if success | false if fail */
static bool meson_irq_calculate_reg_off_and_start_bit(meson_irq_reg_type_t function, size_t irq, uint32_t *reg_offset, uint32_t *start_bit)
{
    if (irq < MESON_GPIO_IRQ_CHANNEL_START || irq >= MESON_GPIO_IRQ_CHANNEL_START + MESON_GPIO_IRQ_CHANNEL_COUNT) {
        return false;
    }

    for (int i = 0; i < MESON_IRQ_FUNC_COUNT; i++) {
        if (irq_config_control[i].function == function) {
            bool is_last = false;
            int k = 0;
            uint32_t bit_stride = meson_irq_bit_strides[function];

            while (!is_last) {
                struct meson_irq_register_data reg_data = irq_config_control[i].registers[k];
                is_last = reg_data.is_last;
                k++;

                if ((uint32_t)irq < reg_data.start_irq_number) {
                    return false;
                }

                uint32_t range = reg_data.end_bit - reg_data.start_bit + 1;
                range /= bit_stride;
                if ((uint32_t)irq > reg_data.start_irq_number + range - 1) {
                    continue;
                }

                *reg_offset = reg_data.register_offset;
                *start_bit = reg_data.start_bit + ((uint32_t)irq - reg_data.start_irq_number) * bit_stride;
                return true;
            }
        }
    }
    return false;
}

static bool meson_gpio_calculate_reg_off_and_start_bit(meson_gpio_reg_type_t function, size_t pin, uint32_t *reg_offset, uint32_t *start_bit)
{
    meson_gpio_bank_t bank = meson_get_gpio_bank(pin);
    if (bank == MESON_GPIO_ERROR_INVALID_PIN) {
        return false;
    }

    for (int i = 0; i < MESON_GPIO_FUNC_COUNT; i++) {
        if (gpio_config_control[i].function == function) {
            for (int j = 0; j < MESON_GPIO_BANK_COUNT; j++) {
                if (gpio_config_control[i].banks[j].bank == bank) {
                    bool is_last = false;
                    int k = 0;
                    uint32_t bit_stride = meson_gpio_bit_strides[function];

                    while (!is_last) {
                        struct meson_gpio_register_data reg_data = gpio_config_control[i].banks[j].registers[k];
                        is_last = reg_data.is_last;
                        k++;

                        uint32_t bank_pin_number = (uint32_t)(pin) - (uint32_t)bank;

                        if (bank_pin_number < reg_data.start_pin_number) {
                            return false;
                        }

                        uint32_t range = reg_data.end_bit - reg_data.start_bit + 1;
                        range /= bit_stride;
                        if (bank_pin_number > reg_data.start_pin_number + range - 1) {
                            continue;
                        }

                        *reg_offset = reg_data.register_offset;
                        *start_bit = reg_data.start_bit + (bank_pin_number - reg_data.start_pin_number) * bit_stride;
                        return true;
                    }
                }
            }
            return false;
        }
    }
    return false;
}

static volatile uint32_t *meson_get_gpio_base_address(size_t pin)
{
    meson_gpio_bank_t bank = meson_get_gpio_bank(pin);

    if (bank == MESON_GPIO_AO) {
        return (volatile uint32_t *)(gpio_ao_regs + GPIO_AO_REGS_BASE_ADDRESS_OFFSET);
    }
    return (volatile uint32_t *)(gpio_regs + GPIO_REGS_BASE_ADDRESS_OFFSET);
}

/* GPIO Operations */

static seL4_MessageInfo_t meson_gpio_set(size_t pin, uint32_t value)
{
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calculate_reg_off_and_start_bit(MESON_GPIO_REG_OUT, pin, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    volatile uint32_t *gpio_base_address = meson_get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = (volatile uint32_t *)((void *)gpio_base_address + reg_offset * 4);

    *final_reg_address &= ~BIT(start_bit);
    *final_reg_address |= (BIT(0) & value) << start_bit;

    return microkit_msginfo_new(0, 0);
}

static seL4_MessageInfo_t meson_gpio_get(size_t pin)
{
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calculate_reg_off_and_start_bit(MESON_GPIO_REG_IN, pin, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    volatile uint32_t *gpio_base_address = meson_get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = (volatile uint32_t *)((void *)gpio_base_address + reg_offset * 4);

    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    return microkit_msginfo_new(value, 0);
}

static seL4_MessageInfo_t meson_gpio_set_direction_output(size_t pin, uint32_t value)
{
    uint32_t reg_offset;
    uint32_t start_bit;

    /* First set the output value */
    if (!meson_gpio_calculate_reg_off_and_start_bit(MESON_GPIO_REG_OUT, pin, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    volatile uint32_t *gpio_base_address = meson_get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = (volatile uint32_t *)((void *)gpio_base_address + reg_offset * 4);

    *final_reg_address &= ~BIT(start_bit);
    *final_reg_address |= (BIT(0) & value) << start_bit;

    /* Then set direction to output (0 = output on meson) */
    if (!meson_gpio_calculate_reg_off_and_start_bit(MESON_GPIO_REG_DIR, pin, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    final_reg_address = (volatile uint32_t *)((void *)gpio_base_address + reg_offset * 4);
    *final_reg_address &= ~BIT(start_bit);

    LOG_DRIVER("meson_gpio_set_direction_output pin=%zu\n", pin);
    print_reg(*final_reg_address);

    return microkit_msginfo_new(0, 0);
}

static seL4_MessageInfo_t meson_gpio_set_direction_input(size_t pin)
{
    uint32_t reg_offset;
    uint32_t start_bit;

    if (!meson_gpio_calculate_reg_off_and_start_bit(MESON_GPIO_REG_DIR, pin, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    volatile uint32_t *gpio_base_address = meson_get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = (volatile uint32_t *)((void *)gpio_base_address + reg_offset * 4);

    /* 1 = input on meson */
    *final_reg_address |= BIT(start_bit);

    LOG_DRIVER("meson_gpio_set_direction_input pin=%zu\n", pin);
    print_reg(*final_reg_address);

    return microkit_msginfo_new(0, 0);
}

static seL4_MessageInfo_t meson_gpio_get_direction(size_t pin)
{
    uint32_t reg_offset;
    uint32_t start_bit;
    if (!meson_gpio_calculate_reg_off_and_start_bit(MESON_GPIO_REG_DIR, pin, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    volatile uint32_t *gpio_base_address = meson_get_gpio_base_address(pin);
    volatile uint32_t *final_reg_address = (volatile uint32_t *)((void *)gpio_base_address + reg_offset * 4);

    /* Meson: 0 = output, 1 = input. SDDF: 0 = output, 1 = input */
    uint32_t value = (*final_reg_address >> start_bit) & BIT(0);

    LOG_DRIVER("meson_gpio_get_direction pin=%zu dir=%u\n", pin, value);
    print_reg(*final_reg_address);

    return microkit_msginfo_new(value, 0);
}

static seL4_MessageInfo_t meson_gpio_set_config(size_t pin, uint32_t config, uint32_t argument)
{
    /* Platform-specific configurations can be handled here */
    /* For now, return not supported for generic config interface */
    (void)pin;
    (void)config;
    (void)argument;
    return error_response(SDDF_GPIO_EOPNOTSUPP);
}

/* IRQ Operations */

static bool meson_set_irq_pin_internal(size_t irq, size_t gpio_pin)
{
    meson_irq_reg_type_t reg_type;
    if (irq == MESON_GPIO_AO_IRQ_0 || irq == MESON_GPIO_AO_IRQ_1) {
        meson_gpio_bank_t bank = meson_get_gpio_bank(gpio_pin);
        if (bank != MESON_GPIO_AO) {
            return false;
        }
        reg_type = MESON_IRQ_REG_AOSEL;
    } else {
        meson_gpio_bank_t bank = meson_get_gpio_bank(gpio_pin);
        if (bank == MESON_GPIO_ERROR_INVALID_PIN || bank == MESON_GPIO_TEST_N) {
            return false;
        }
        reg_type = MESON_IRQ_REG_SEL;
    }

    uint32_t reg_offset;
    uint32_t start_bit;

    if (!meson_irq_calculate_reg_off_and_start_bit(reg_type, irq, &reg_offset, &start_bit)) {
        return false;
    }

    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address = (volatile uint32_t *)((void *)irq_base_address + reg_offset * 4);

    *final_reg_address &= ~BIT_MASK(start_bit, start_bit + meson_irq_bit_strides[reg_type]);
    *final_reg_address |= (BIT_MASK(0, 0 + meson_irq_bit_strides[reg_type]) & gpio_pin) << start_bit;

    return true;
}

static seL4_MessageInfo_t meson_irq_enable(size_t irq)
{
    int irq_idx = irq - MESON_GPIO_IRQ_CHANNEL_START;
    irq_enabled[irq_idx] = true;
    microkit_irq_ack(irq);

    return microkit_msginfo_new(0, 0);
}

static seL4_MessageInfo_t meson_irq_disable(size_t irq)
{
    int irq_idx = irq - MESON_GPIO_IRQ_CHANNEL_START;
    irq_enabled[irq_idx] = false;

    return microkit_msginfo_new(0, 0);
}

static seL4_MessageInfo_t meson_irq_set_type(size_t irq, uint32_t type)
{
    volatile uint32_t *irq_base_address = (void *)(interupt_control_regs + IRQ_CONTROL_REGS_BASE_ADDRESS_OFFSET);
    volatile uint32_t *final_reg_address;
    uint32_t reg_offset;
    uint32_t start_bit;

    /* Handle both-edge enable register */
    if (!meson_irq_calculate_reg_off_and_start_bit(MESON_IRQ_REG_BOTHEDGEEN, irq, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    final_reg_address = (volatile uint32_t *)((void *)irq_base_address + reg_offset * 4);

    /* Clear both-edge bit first */
    *final_reg_address &= ~BIT(start_bit);

    if (type == SDDF_IRQ_TYPE_EDGE_BOTH) {
        *final_reg_address |= BIT(start_bit);
        return microkit_msginfo_new(0, 0);
    }

    /* Handle edge register */
    if (!meson_irq_calculate_reg_off_and_start_bit(MESON_IRQ_REG_EDGE, irq, &reg_offset, &start_bit)) {
        return error_response(SDDF_GPIO_EINVAL);
    }

    final_reg_address = (volatile uint32_t *)((void *)irq_base_address + reg_offset * 4);

    if (type == SDDF_IRQ_TYPE_LEVEL_HIGH || type == SDDF_IRQ_TYPE_LEVEL_LOW) {
        /* Level triggered: edge bit = 0 */
        *final_reg_address &= ~BIT(start_bit);

        /* Handle polarity for level */
        if (!meson_irq_calculate_reg_off_and_start_bit(MESON_IRQ_REG_POL, irq, &reg_offset, &start_bit)) {
            return error_response(SDDF_GPIO_EINVAL);
        }

        final_reg_address = (volatile uint32_t *)((void *)irq_base_address + reg_offset * 4);

        if (type == SDDF_IRQ_TYPE_LEVEL_LOW) {
            *final_reg_address |= BIT(start_bit);
        } else {
            *final_reg_address &= ~BIT(start_bit);
        }

        return microkit_msginfo_new(0, 0);
    }

    if (type == SDDF_IRQ_TYPE_EDGE_RISING || type == SDDF_IRQ_TYPE_EDGE_FALLING) {
        /* Edge triggered: edge bit = 1 */
        *final_reg_address |= BIT(start_bit);

        /* Handle polarity */
        if (!meson_irq_calculate_reg_off_and_start_bit(MESON_IRQ_REG_POL, irq, &reg_offset, &start_bit)) {
            return error_response(SDDF_GPIO_EINVAL);
        }

        final_reg_address = (volatile uint32_t *)((void *)irq_base_address + reg_offset * 4);

        if (type == SDDF_IRQ_TYPE_EDGE_FALLING) {
            *final_reg_address |= BIT(start_bit);
        } else {
            *final_reg_address &= ~BIT(start_bit);
        }

        return microkit_msginfo_new(0, 0);
    }

    return error_response(SDDF_GPIO_EINVAL);
}

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    uint32_t label = microkit_msginfo_get_label(msginfo);
    uint32_t interface_function = label & SDDF_REQUEST_INTERFACE_MASK;
    uint32_t value = gpio_decode_value(label);

    int pin = gpio_driver_channel_mappings[ch].pin;

    /* Unexpected channel */
    if (pin < 0) {
        return error_response(SDDF_GPIO_EPERM);
    }

    switch (interface_function) {
    case SDDF_GPIO_SET: {
        return meson_gpio_set(pin, value);
    }
    case SDDF_GPIO_GET: {
        return meson_gpio_get(pin);
    }
    case SDDF_GPIO_DIRECTION_OUTPUT: {
        return meson_gpio_set_direction_output(pin, value);
    }
    case SDDF_GPIO_DIRECTION_INPUT: {
        return meson_gpio_set_direction_input(pin);
    }
    case SDDF_GPIO_GET_DIRECTION: {
        return meson_gpio_get_direction(pin);
    }
    case SDDF_GPIO_SET_CONFIG: {
        uint32_t argument = seL4_GetMR(0);
        return meson_gpio_set_config(pin, value, argument);
    }
    case SDDF_GPIO_IRQ_ENABLE: {
        if (check_irq_permission(ch)) {
            int irq = gpio_driver_channel_mappings[ch].irq;
            return meson_irq_enable(irq);
        }
        return error_response(SDDF_GPIO_EPERM);
    }
    case SDDF_GPIO_IRQ_DISABLE: {
        if (check_irq_permission(ch)) {
            int irq = gpio_driver_channel_mappings[ch].irq;
            return meson_irq_disable(irq);
        }
        return error_response(SDDF_GPIO_EPERM);
    }
    case SDDF_GPIO_IRQ_SET_TYPE: {
        if (check_irq_permission(ch)) {
            int irq = gpio_driver_channel_mappings[ch].irq;
            return meson_irq_set_type(irq, value);
        }
        return error_response(SDDF_GPIO_EPERM);
    }
    default:
        LOG_DRIVER("Unknown request %u to gpio from channel %u\n", label, ch);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
}

void init(void)
{
    LOG_DRIVER("Driver Init!\n");

    /* Initialize IRQ enabled state */
    for (int i = 0; i < MESON_GPIO_IRQ_CHANNEL_COUNT; i++) {
        irq_enabled[i] = false;
        driver_to_client_channel_mappings[i] = -1;
    }

    /* Configure gpio channel mappings */
    for (int i = 0; i < 62; i++) {
        if (gpio_driver_channel_mappings[i].pin == -1
            && gpio_driver_channel_mappings[i].irq != -1) {
            LOG_DRIVER_ERR("Failed to config gpio_driver_channel_mappings[%d] because GPIO pin must be set if IRQ is set!\n", i);
            while (1) {}
        } else if (gpio_driver_channel_mappings[i].pin == -1) {
            continue;
        }

        int gpio_pin = gpio_driver_channel_mappings[i].pin;

        /* If GPIO pin is configured make sure its only configured to a client channel once */
        int count = 0;
        for (int j = 0; j < 62; j++) {
            if (gpio_pin == gpio_driver_channel_mappings[j].pin) {
                count++;
            }
        }
        if (count != 1) {
            LOG_DRIVER_ERR("Failed to config gpio_driver_channel_mappings[%d] because GPIO pin is not configured ONLY ONCE\n", i);
            while (1) {}
        }

        /* Check if IRQ has been configured for this GPIO */
        if (gpio_driver_channel_mappings[i].irq != -1) {
            int irq = gpio_driver_channel_mappings[i].irq;
            LOG_DRIVER("IRQ %d\n", irq);

            /* Check if its a valid irq configuration */
            if (!meson_is_valid_irq_config(irq)) {
                LOG_DRIVER_ERR("Failed to config gpio_driver_channel_mappings[%d] because failed to config irq!\n", i);
                while (1) {}
            }

            /* Ensure IRQ channel is not configured to another channel */
            count = 0;
            for (int j = 0; j < 62; j++) {
                if (irq == gpio_driver_channel_mappings[j].irq) {
                    count++;
                }
            }
            if (count != 1) {
                LOG_DRIVER_ERR("Failed to config gpio_driver_channel_mappings[%d] because IRQ is not configured ONLY ONCE\n", i);
                while (1) {}
            }

            /* Configure IRQ pin mapping with hardware */
            if (!meson_set_irq_pin_internal(irq, gpio_pin)) {
                LOG_DRIVER_ERR("Failed to config gpio_driver_channel_mappings[%d] IRQ pin mapping!\n", i);
                while (1) {}
            }

            /* Assign channel to the gpio pin */
            driver_to_client_channel_mappings[irq - MESON_GPIO_IRQ_CHANNEL_START] = i;

            /* ACK the IRQ so we can receive further IRQs */
            microkit_irq_ack(irq);
        }
    }

    LOG_DRIVER("Driver Init Complete!\n");
}
