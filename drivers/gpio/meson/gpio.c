/*
 * Copyright 2023, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <sddf/gpio/gpio.h>
#include <sddf/gpio/meson/gpio.h>
#include <gpio_config.h>
#include "driver.h"

#ifndef GPIO_CONFIG_H
    #error "Must define GPIO channel mappings for clients in gpio config"
#endif

_Static_assert(sizeof(cli_channel_mappings) == EXPECTED_SIZE, "cli_channel_mappings does not have the expected size");
_Static_assert(sizeof(cli_channel_mappings[0]) == sizeof(int[3]), "cli_channel_mappings elements must be of type int[2]");
// _Static_assert(cli_channel_mappings[0][CHANNEL_MAPPINGS_CHANNEL_NUMBER_INDEX] == 0, "cli_channel_mappings must start at channel 0");

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("GPIO DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("GPIO DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// Hardware memory
uintptr_t gpio_regs;
uintptr_t gpio_ao_regs;
uintptr_t interupt_control_regs;

// Device Channel Mappings
static int device_channel_mappings[MESON_IRQ_CHANNEL_COUNT];

void init(void)
{
    // Initialise Interface

    // NOTE: the hardware has been wrong in some situations.
    // Hence this intialisation is subject to change.
    // For instance you can enable output for GPIO_Z pins 14:15 but
    // cant read input or set ouput for GPIO_Z pins 14:15 according to datasheet

    static struct meson_gpio_bank out[] = {
        MESON_GPIO_BANK( GPIO_AO, MESON_GPIO_REGISTER_DATA(AO_GPIO_O, 0, 11, 0, true) ),
        MESON_GPIO_BANK( GPIO_Z, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO4_O, 0, 13, 0, true) ),
        MESON_GPIO_BANK( GPIO_H, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO3_O, 4, 7, 4, true) ),
        MESON_GPIO_BANK( BOOT, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO0_O, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_C, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO1_O, 0, 6, 0, true) ),
        MESON_GPIO_BANK( GPIO_A, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO5_O, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_X, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO2_O, 0, 19, 0, true) ),
        MESON_GPIO_BANK( GPIO_E, MESON_GPIO_REGISTER_DATA( AO_GPIO_O, 16, 18, 0, true) ),
        MESON_GPIO_BANK( TEST_N, MESON_GPIO_REGISTER_DATA( AO_GPIO_O, 31, 31, 0, true) )
    };
    static struct meson_gpio_bank in[] = {
        MESON_GPIO_BANK( GPIO_AO, MESON_GPIO_REGISTER_DATA(AO_GPIO_I, 0, 11, 0, true) ),
        MESON_GPIO_BANK( GPIO_Z, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO4_I, 0, 13, 0, true) ),
        MESON_GPIO_BANK( GPIO_H, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO3_I, 0, 8, 0, true) ),
        MESON_GPIO_BANK( BOOT, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO0_I, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_C, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO1_I, 0, 7, 0, true) ),
        MESON_GPIO_BANK( GPIO_A, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO5_I, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_X, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO2_I, 0, 19, 0, true) ),
        MESON_GPIO_BANK( GPIO_E, MESON_GPIO_REGISTER_DATA( AO_GPIO_I, 16, 18, 0, true) ),
        MESON_GPIO_BANK( TEST_N, MESON_GPIO_REGISTER_DATA( AO_GPIO_I, 31, 31, 0, true) )
    };
    static struct meson_gpio_bank dir[] = {
        MESON_GPIO_BANK( GPIO_AO, MESON_GPIO_REGISTER_DATA(AO_GPIO_O_EN_N, 0, 11, 0, true) ),
        MESON_GPIO_BANK( GPIO_Z, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO4_I, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_H, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO3_EN_N, 0, 8, 0, true) ),
        MESON_GPIO_BANK( BOOT, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO0_EN_N, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_C, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO1_EN_N, 0, 7, 0, true) ),
        MESON_GPIO_BANK( GPIO_A, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO5_EN_N, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_X, MESON_GPIO_REGISTER_DATA( PREG_PAD_GPIO2_EN_N, 0, 19, 0, true) ),
        MESON_GPIO_BANK( GPIO_E, MESON_GPIO_REGISTER_DATA( AO_GPIO_O_EN_N, 16, 18, 0, true) ),
        MESON_GPIO_BANK( TEST_N, MESON_GPIO_REGISTER_DATA( AO_GPIO_O_EN_N, 31, 31, 0, true) )
    };
    static struct meson_gpio_bank pullen[] = {
        MESON_GPIO_BANK( GPIO_AO, MESON_GPIO_REGISTER_DATA(AO_RTI_PULL_UP_EN_REG, 0, 11, 0, true) ),
        MESON_GPIO_BANK( GPIO_Z, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_EN_REG4, 0, 13, 0, true) ),
        MESON_GPIO_BANK( GPIO_H, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_EN_REG3, 4, 7, 4, true) ),
        MESON_GPIO_BANK( BOOT, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_EN_REG0, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_C, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_EN_REG1, 0, 6, 0, true) ),
        MESON_GPIO_BANK( GPIO_A, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_EN_REG5, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_X, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_EN_REG2, 0, 19, 0, true) ),
        MESON_GPIO_BANK( GPIO_E, MESON_GPIO_REGISTER_DATA( AO_RTI_PULL_UP_EN_REG, 16, 18, 0, true) ),
        MESON_GPIO_BANK( TEST_N, MESON_GPIO_REGISTER_DATA( AO_RTI_PULL_UP_EN_REG, 31, 31, 0, true) )
    };
    static struct meson_gpio_bank pull[] = {
        MESON_GPIO_BANK( GPIO_AO, MESON_GPIO_REGISTER_DATA(AO_RTI_PULL_UP_REG, 0, 11, 0, true) ),
        MESON_GPIO_BANK( GPIO_Z, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_REG4, 0, 13, 0, true) ),
        MESON_GPIO_BANK( GPIO_H, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_REG3, 4, 7, 4, true) ),
        MESON_GPIO_BANK( BOOT, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_REG0, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_C, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_REG1, 0, 6, 0, true) ),
        MESON_GPIO_BANK( GPIO_A, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_REG5, 0, 15, 0, true) ),
        MESON_GPIO_BANK( GPIO_X, MESON_GPIO_REGISTER_DATA( PAD_PULL_UP_REG2, 0, 19, 0, true) ),
        MESON_GPIO_BANK( GPIO_E, MESON_GPIO_REGISTER_DATA( AO_RTI_PULL_UP_REG, 16, 18, 0, true) ),
        MESON_GPIO_BANK( TEST_N, MESON_GPIO_REGISTER_DATA( AO_RTI_PULL_UP_REG, 31, 31, 0, true) )
    };
    static struct meson_gpio_bank ds[] = {
        MESON_GPIO_BANK( GPIO_AO, MESON_GPIO_REGISTER_DATA( AO_PAD_DS_A, 0, 23, 0, true) ),
        MESON_GPIO_BANK( GPIO_Z, MESON_GPIO_REGISTER_DATA( PAD_DS_REG4A, 0, 27, 0, true) ),
        MESON_GPIO_BANK( GPIO_H, MESON_GPIO_REGISTER_DATA( PAD_DS_REG3A, 8, 15, 4, true) ),
        MESON_GPIO_BANK( BOOT, MESON_GPIO_REGISTER_DATA( PAD_DS_REG0A, 0, 31, 0, true) ),
        MESON_GPIO_BANK( GPIO_C, MESON_GPIO_REGISTER_DATA( PAD_DS_REG1A, 0, 13, 0, true) ),
        MESON_GPIO_BANK( GPIO_A, MESON_GPIO_REGISTER_DATA( PAD_DS_REG5A, 0, 31, 0, true) ),
        MESON_GPIO_BANK( GPIO_X,
            MESON_GPIO_REGISTER_DATA( PAD_DS_REG2A, 0, 31, 0, false),
            MESON_GPIO_REGISTER_DATA( PAD_DS_REG2B, 0, 5, 16, false),
            MESON_GPIO_REGISTER_DATA( PAD_DS_REG2B, 4, 5, 19, true) // pin 18 and 19 share the same bit
        ),
        MESON_GPIO_BANK( GPIO_E, MESON_GPIO_REGISTER_DATA( AO_PAD_DS_B, 0, 5, 0, true) ),
        MESON_GPIO_BANK( TEST_N, MESON_GPIO_REGISTER_DATA( AO_PAD_DS_B, 28, 29, 0, true)
            // what does reset_n do?
        )
    };

    gpio_config_control[MESON_GPIO_REG_PULLEN] = pullen;
    gpio_config_control[MESON_GPIO_REG_PULL] = pull;
    gpio_config_control[MESON_GPIO_REG_DIR] = dir;
    gpio_config_control[MESON_GPIO_REG_OUT] = out;
    gpio_config_control[MESON_GPIO_REG_IN] = in;
    gpio_config_control[MESON_GPIO_REG_DS] = ds;

    static struct meson_irq_register_data bothedge[] = {
        MESON_IRQ_REGISTER_DATA( GPIO_INTERUPT_EDGE_AND_POLARITY, 24, 31, 0, false ),
        MESON_IRQ_REGISTER_DATA( AO_IRQ_GPIO_REG, 20, 21, 8, true )
    };
    static struct meson_irq_register_data edge[] = {
        MESON_IRQ_REGISTER_DATA( GPIO_INTERUPT_EDGE_AND_POLARITY, 0, 7, 0, false ),
        MESON_IRQ_REGISTER_DATA( AO_IRQ_GPIO_REG, 18, 19, 8, true )
    };
    static struct meson_irq_register_data pol[] = {
        MESON_IRQ_REGISTER_DATA( GPIO_INTERUPT_EDGE_AND_POLARITY, 24, 31, 0, false ),
        MESON_IRQ_REGISTER_DATA( AO_IRQ_GPIO_REG, 16, 17, 8, true )
    };
    static struct meson_irq_register_data fil[] = {
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 0, 2, 0, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 4, 6, 1, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 8, 10, 2, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 12, 14, 3, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 16, 18, 4, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 20, 22, 5, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 24, 26, 6, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_FILTER_SELECT, 28, 30, 7, false ),
        MESON_IRQ_REGISTER_DATA( AO_IRQ_GPIO_REG, 8, 10, 8, false ),
        MESON_IRQ_REGISTER_DATA( AO_IRQ_GPIO_REG, 12, 14, 9, true )
    };
    static struct meson_irq_register_data aosel[] = {
        MESON_IRQ_REGISTER_DATA( AO_IRQ_GPIO_REG, 0, 7, 8, true )
    };
    static struct meson_irq_register_data sel[] = {
        MESON_IRQ_REGISTER_DATA( GPIO_0_3_PIN_SELECT, 0, 31, 0, false ),
        MESON_IRQ_REGISTER_DATA( GPIO_4_7_PIN_SELECT, 0, 31, 4, true )
    };

    irq_config_control[MESON_IRQ_REG_BOTHEDGEEN] = bothedge;
    irq_config_control[MESON_IRQ_REG_EDGE] = edge;
    irq_config_control[MESON_IRQ_REG_POL] = pol;
    irq_config_control[MESON_IRQ_REG_FIL] = fil;
    irq_config_control[MESON_IRQ_REG_AOSEL] = aosel;
    irq_config_control[MESON_IRQ_REG_SEL] = sel;

    // Initialise dev <-> drv channel to correct gpio based on config file
    for (int i = 0; i < MESON_IRQ_CHANNEL_COUNT; i++) {
        device_channel_mappings[i] = -1;
    }

    for (int i = 0; i < NUM_CLI_GPIO_CHANNELS; i++) {
        if (cli_channel_mappings[i][CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX] != -1) {
            // It has been configured
            int meson_channel = cli_channel_mappings[i][CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX] - DEV_IRQ_CHANNEL_OFFSET;
            device_channel_mappings[meson_channel] = cli_channel_mappings[i][CHANNEL_MAPPINGS_CHANNEL_NUMBER_INDEX];
            seL4_MessageInfo_t msg_info = meson_set_irq_pin(meson_channel, cli_channel_mappings[i][CHANNEL_MAPPINGS_GPIO_PIN_INDEX]);
            if (microkit_msginfo_get_label(msginfo) == FAILURE) {
                size_t error = microkit_mr_get(RES_GPIO_IRQ_ERROR_SLOT);
                LOG_CLIENT_ERR("failed to set irq channel of gpio with error %d!\n", error);
            }
        }
    }

    microkit_dbg_puts("Driver initialised.\n");
}

/* Will not notify channel if not configured */
void notify_client_channel(int ch) {
    if (device_channel_mappings[ch] != -1) {
        microkit_notify(device_channel_mappings[ch]);
    }
    LOG_DRIVER_ERR("No corresponding client channel configured with device IRQ!\n")
}

void notified(microkit_channel ch)
{
    switch (ch) {
        case DEV_GPIO_IRQ_0_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_0_CH);
            break;
        case DEV_GPIO_IRQ_1_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_1_CH);
            break;
        case DEV_GPIO_IRQ_2_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_2_CH);
            break;
        case DEV_GPIO_IRQ_3_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_3_CH);
            break;
        case DEV_GPIO_IRQ_4_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_4_CH);
            break;
        case DEV_GPIO_IRQ_5_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_5_CH);
            break;
        case DEV_GPIO_IRQ_6_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_6_CH);
            break;
        case DEV_GPIO_IRQ_7_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_IRQ_7_CH);
            break;
        case DEV_GPIO_AO_IRQ_0_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_AO_IRQ_0_CH);
            break;
        case DEV_GPIO_AO_IRQ_1_CH:
            microkit_irq_ack(ch);
            notify_client_channel(DEV_GPIO_AO_IRQ_1_CH);
            break;
        default:
            microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
}

static seL4_MessageInfo_t invalid_request_error_message(gpio_irq_error_t error) {
    seL4_MessageInfo_t error_message = microkit_msginfo_new(REQ_FAILURE, 1);
    microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, (size_t)error);
    LOG_DRIVER_ERR("Invalid Request : %d", error);
    return error_message;
}

static gpio_meson_bank_t meson_get_gpio_bank(size_t pin) {
    if (pin_number < GPIO_Z) return GPIO_AO;
    if (pin_number < GPIO_H) return GPIO_Z;
    if (pin_number < BOOT) return GPIO_H;
    if (pin_number < GPIO_C) return BOOT;
    if (pin_number < GPIO_A) return GPIO_C;
    if (pin_number < GPIO_X) return GPIO_A;
    if (pin_number < GPIO_E) return GPIO_X;
    if (pin_number < TEST_N) return GPIO_E;
    if (pin_number < ERROR_INVALID_PIN) return TEST_N;
    return ERROR_INVALID_PIN;
}

/**
 * meson_gpio_calc_reg_and_bits() - calculate bits for a pin and function.
 * function should be valid
 *
 * @reg:            double pointer to hardware register to manipulate
 * @start_bit:	    the offset in the register we want
 * @returns:        true if found pin in registers, false otherwise
 */
static bool meson_gpio_calc_reg_and_bits(meson_reg_type_t function, size_t pin, volatile uint32_t **reg, uint32_t *start_bit) {
    // check if pin is too high
    gpio_meson_bank_t bank = meson_get_gpio_bank(pin);
    if (bank == ERROR_INVALID_PIN) {
        return false;
    }

    // find bank
    for (int bank_count = 0; bank_count < MESON_GPIO_BANK_COUNT; bank_count++) {
        if (gpio_config[function][bank_count].bank == bank) {
            // find register
            bool is_last = false;
            int index = 0;
            uint32_t bit_stride = meson_gpio_bit_strides[function];
            while (!is_last) {
                struct MESON_GPIO_REGISTER_DATA reg_data = gpio_config[function][bank_count].registers[index];
                is_last = reg_data.is_last;
                index++;

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
                // its in this register // find what pins
                *reg = reg_data.register_offset;
                *start_bit = reg_data.start_bit + (bank_pin_number - reg_data.start_pin_number /* get the amount of pins after start bit */) * bit_stride;
                return true;
            }
            // didnt find
            return false;
        }
    }

    return false;
}

/**
 * meson_irq_calc_reg_and_bits() - calculate bits for a channel and function.
 * function should be valid
 *
 * @reg:            double pointer to hardware register to manipulate
 * @start_bit:	    the offset in the register we want
 * @returns:        true if found channel in registers, false otherwise
 */
static bool meson_irq_calc_reg_and_bits(meson_irq_reg_type_t function, size_t channel, volatile uint32_t **reg, uint32_t *start_bit) {
    // check if channel is too high
    if (channel >= MESON_IRQ_CHANNEL_COUNT) {
        return false;
    }

    // find register
    bool is_last = false;
    int index = 0;
    uint32_t bit_stride = meson_irq_bit_strides[function];
    while (!is_last) {
        struct MESON_GPIO_REGISTER_DATA reg_data = meson_irq_control[function];
        is_last = reg_data.is_last;
        index++;

        // see if the pin is in this register range
        if ((uint32_t)(channel) < reg_data.start_channel_number) {
            return false;
        }
        uint32_t range = reg_data.end_bit - reg_data.start_bit + 1;
        range /= bit_stride;
        if ((uint32_t)(channel) > reg_data.start_channel_number + range - 1) {
            continue; // check next register
        }
        // its in this register // find what pins
        *reg = reg_data.register_offset;
        *start_bit = reg_data.start_bit + ((uint32_t)(channel) - reg_data.start_channel_number /* get the amount of pins after start bit */) * bit_stride;
        return true;
    }

    return false;
}

seL4_MessageInfo_t meson_get_gpio_output(size_t pin) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_OUT, pin, &reg, &start_bit)) {
        LOG_DRIVER_ERR("Invalid Request : %d", INVALID_PIN);
        return invalid_request_error_message(INVALID_PIN);
    }

    uint32_t value = (*reg >> start_bit) & BIT(0);

    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    microkit_mr_set(RES_GPIO_VALUE_SLOT, value);
    return response;
}

seL4_MessageInfo_t meson_set_gpio_output(size_t pin, size_t value) {
    if (value != 0 && value != 1) {
        return invalid_request_error_message(INVALID_VALUE);
        LOG_DRIVER_ERR("Invalid Request : %d", INVALID_VALUE);
    }

    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_OUT, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    *reg &= ~BIT(start_bit);
    *reg |= BIT(start_bit) & value;

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t meson_get_gpio_input(size_t pin) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_IN, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    uint32_t value = (*reg >> start_bit) & BIT(0);

    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    microkit_mr_set(RES_GPIO_VALUE_SLOT, value);
    return response;
}

seL4_MessageInfo_t meson_get_gpio_direction(size_t pin) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DIR, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    uint32_t value = (*reg >> start_bit) & BIT(0);
    size_t direction_value = value == 0 ? DIRECTION_OUTPUT : DIRECTION_INPUT;

    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    microkit_mr_set(RES_GPIO_VALUE_SLOT, direction_value);
    return response;
}

seL4_MessageInfo_t meson_set_gpio_direction(size_t pin, size_t value) {
    if (value != DIRECTION_OUTPUT && value != DIRECTION_INPUT) {
        return invalid_request_error_message(INVALID_VALUE);
    }

    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DIR, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    *reg &= ~BIT(start_bit);
    *reg |= BIT(start_bit) & value;

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t meson_get_gpio_pull(size_t pin) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULLEN, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    uint32_t value = (*reg >> start_bit) & BIT(0);

    if (value == 0) {
        seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
        microkit_mr_set(RES_GPIO_VALUE_SLOT, NO_PULL);
        return response;
    }

    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULL, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    value = (*reg >> start_bit) & BIT(0);
    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    if (value == 0) {
        microkit_mr_set(RES_GPIO_VALUE_SLOT, PULL_DOWN);
    } else {
        microkit_mr_set(RES_GPIO_VALUE_SLOT, PULL_UP);
    }
    return response;
}

seL4_MessageInfo_t meson_set_gpio_pull(size_t pin, size_t value) {
    if (value != PULL_UP && value != PULL_DOWN && value != NO_PULL) {
        return invalid_request_error_message(INVALID_VALUE);
    }

    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULLEN, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    // set actual value
    if (value == NO_PULL) {
        *reg &= ~BIT(start_bit);
        return microkit_msginfo_new(SUCCESS, 0);
    }

    *reg |= BIT(start_bit); // enables

    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_PULL, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    if (value == PULL_DOWN) {
        *reg &= ~BIT(start_bit);
    } else {
        *reg |= BIT(start_bit);
    }

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t meson_get_gpio_drive_strength(size_t pin) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DS, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    uint32_t value = (*reg >> start_bit) & BIT_MASK(0, meson_gpio_bit_strides[MESON_GPIO_REG_DS]);

    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    microkit_mr_set(RES_GPIO_VALUE_SLOT, value);
    return response;
}

seL4_MessageInfo_t meson_set_gpio_drive_strength(size_t pin, size_t value) {
    if (value != DS_500UA && value != DS_2500UA && value != DS_3000UA && value != DS_4000UA) {
        return invalid_request_error_message(INVALID_VALUE);
    }

    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_gpio_calc_reg_and_bits(MESON_GPIO_REG_DS, pin, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_PIN);
    }

    uint32_t shifted_value = value << start_bit;
    *reg &= ~MASK(start_bit, start_bit + meson_gpio_bit_strides[MESON_GPIO_REG_DS]);
    *reg |= shifted_value;

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t meson_get_irq_pin(size_t channel) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    meson_irq_reg_type_t reg_type;

    if (channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) {
        reg_type = MESON_IRQ_REG_AOSEL;
    } else {
        reg_type = MESON_IRQ_REG_SEL;
    }

    if (!meson_irq_calc_reg_and_bits(reg_type, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    uint32_t value = (*reg >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[reg_type]);

    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    microkit_mr_set(RES_IRQ_VALUE_SLOT, value);
    return response;
}

seL4_MessageInfo_t meson_set_irq_pin(size_t channel, size_t value) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    meson_irq_reg_type_t reg_type;

    if (channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) {
        gpio_meson_bank_t bank = meson_get_gpio_bank(value);
        if (bank != GPIO_AO) {
            return invalid_request_error_message(INVALID_VALUE);
        }
        reg_type = MESON_IRQ_REG_AOSEL;
    } else {
        gpio_meson_bank_t bank = meson_get_gpio_bank(value);
        if (bank == ERROR_INVALID_PIN || bank == TEST_N) {
            return invalid_request_error_message(INVALID_VALUE);
        }
        reg_type = MESON_IRQ_REG_SEL;
    }

    if (!meson_irq_calc_reg_and_bits(reg_type, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    uint32_t shifted_value = value << start_bit;
    *reg &= ~MASK(start_bit, start_bit + meson_irq_bit_strides[reg_type]);
    *reg |= shifted_value;

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t meson_get_irq_edge(size_t channel) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_BOTHEDGEEN, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    uint32_t value = (*reg >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[BOTH_RISING_FALLING]);
    if (value == 1) {
        seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
        microkit_mr_set(RES_IRQ_VALUE_SLOT, BOTH_RISING_FALLING);
        return response;
    }

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_EDGE, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    value = (*reg >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[MESON_IRQ_REG_EDGE]);
    if (value == 0) {
        seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
        microkit_mr_set(RES_IRQ_VALUE_SLOT, LEVEL);
        return response;
    }

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_POL, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    value = (*reg >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[MESON_IRQ_REG_POL]);
    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    if (value == 1) {
        microkit_mr_set(RES_IRQ_VALUE_SLOT, FALLING);
    } else {
        microkit_mr_set(RES_IRQ_VALUE_SLOT, RISING);
    }
    return response;
}

seL4_MessageInfo_t meson_set_irq_edge(size_t channel, size_t value) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;

    if (value != BOTH_RISING_FALLING && value != RISING && value != FALLING && value != LEVEL) {
        return invalid_request_error_message(INVALID_VALUE);
    }

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_BOTHEDGEEN, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    if (value == BOTH_RISING_FALLING) {
        *reg |= BIT(start_bit);
        return microkit_msginfo_new(SUCCESS, 0);
    }

    *reg &= ~BIT(start_bit); // disable
    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_EDGE, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    if (value == LEVEL) {
        *reg &= ~BIT(start_bit); // disable
        return microkit_msginfo_new(SUCCESS, 0);
    }

    *reg |= BIT(start_bit); // enable
    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_POL, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    if (value == RISING) {
        *reg &= ~BIT(start_bit);
    } else {
        *reg |= BIT(start_bit);
    }

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t meson_get_irq_filter(size_t channel) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;

    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_FIL, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    uint32_t value = (*reg >> start_bit) & BIT_MASK(0, meson_irq_bit_strides[MESON_IRQ_REG_FIL]);

    seL4_MessageInfo_t response = microkit_msginfo_new(SUCCESS, 1);
    if ((channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) && value == 1) {
        microkit_mr_set(RES_IRQ_VALUE_SLOT, FILTER_2600NS);
    } else {
        microkit_mr_set(RES_IRQ_VALUE_SLOT, value);
    }

    return response;
}

seL4_MessageInfo_t meson_set_irq_filter(size_t channel, size_t value) {
    volatile uint32_t *reg = NULL;
    uint32_t start_bit = 0;
    if (!meson_irq_calc_reg_and_bits(MESON_IRQ_REG_FIL, channel, &reg, &start_bit)) {
        return invalid_request_error_message(INVALID_CONFIG_ENTRY);
    }

    if (channel == GPIO_AO_IRQ_0 || channel == GPIO_AO_IRQ_1) {
        if (value == FILTER_2600NS) {
            *reg |= BIT(start_bit);
        } else if (value == FILTER_0NS) {
            *reg &= ~BIT(start_bit);
        } else {
            return invalid_request_error_message(INVALID_VALUE);
        }
    } else {
        *reg &= ~MASK(start_bit, start_bit + meson_irq_bit_strides[MESON_IRQ_REG_FIL]);
        if (!(FILTER_0NS <= value && FILTER_2331NS >= value)) {
            return invalid_request_error_message(INVALID_VALUE);
        }
        uint32_t shifted_value = value << start_bit;;
        *reg |= shifted_value;
    }

    return microkit_msginfo_new(SUCCESS, 0);
}

seL4_MessageInfo_t handle_get_gpio_request(size_t pin, size_t config) {
    switch (config) {
        case OUTPUT:
            return meson_get_gpio_output(pin);
        case INPUT:
            return meson_get_gpio_input(pin);
        case DIRECTION:
            return meson_get_gpio_direction(pin);
        case PULL:
            return meson_get_gpio_pull(pin);
        case DRIVE_STRENGTH:
            return meson_get_gpio_drive_strength(pin);
        default:
            return invalid_request_error_message(INVALID_CONFIG);
    }
}

seL4_MessageInfo_t handle_set_gpio_request(size_t pin, size_t config, size_t value) {
   switch (config) {
        case OUTPUT:
            return meson_set_gpio_output(pin, value);
        case DIRECTION:
            return meson_set_gpio_direction(pin, value);
        case PULL:
            return meson_set_gpio_pull(pin, value);
        case DRIVE_STRENGTH:
            return meson_set_gpio_drive_strength(pin, value);
        default:
            return invalid_request_error_message(INVALID_CONFIG);
    }
}

seL4_MessageInfo_t handle_get_irq_request(size_t channel, size_t config) {
    switch (config) {
        case PIN:
            return meson_get_irq_pin(channel);
        case EDGE:
            return meson_get_irq_edge(channel);
        case FILTER:
            return meson_get_irq_filter(channel);
        default:
            return invalid_request_error_message(INVALID_CONFIG);
    }
}

seL4_MessageInfo_t handle_set_irq_request(size_t channel, size_t config, size_t value) {
   switch (config) {
        case EDGE:
            return meson_set_irq_edge(channel, value);
        case FILTER:
            return meson_set_irq_filter(channel, value);
        default:
            return invalid_request_error_message(INVALID_CONFIG);
    }
}

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t count = microkit_msginfo_get_count(msginfo);
    size_t config, pin, meson_channel, value;

    switch (label) {
        case GET_GPIO:
            if (count != 1) {
                return invalid_request_error_message(INVALID_NUM_ARGS);
            }
            // check mapping
            if (cli_channel_mappings[ch][CHANNEL_MAPPINGS_GPIO_PIN_INDEX] < 0) {
                return invalid_request_error_message(INVALID_CONFIG_ENTRY);
            }
            config = microkit_mr_get(REQ_GPIO_CONFIG_SLOT);
            pin = cli_channel_mappings[ch][CHANNEL_MAPPINGS_GPIO_PIN_INDEX];
            return handle_get_gpio_request(pin, config);
        case GET_IRQ:
            if (count != 1) {
                return invalid_request_error_message(INVALID_NUM_ARGS);
            }
            // check mapping
            if (cli_channel_mappings[ch][CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX] < 0) {
                return invalid_request_error_message(INVALID_CONFIG_ENTRY);
            }
            config = microkit_mr_get(REQ_GPIO_CONFIG_SLOT);
            meson_channel = cli_channel_mappings[ch][CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX] - DEV_IRQ_CHANNEL_OFFSET;
            return handle_get_irq_request(meson_channel, config);
        case SET_GPIO:
            if (count != 2) {
                return invalid_request_error_message(INVALID_NUM_ARGS);
            }
            // check mapping
            if (cli_channel_mappings[ch][CHANNEL_MAPPINGS_GPIO_PIN_INDEX] < 0) {
                return invalid_request_error_message(INVALID_CONFIG_ENTRY);
            }
            config = microkit_mr_get(REQ_GPIO_CONFIG_SLOT);
            pin = cli_channel_mappings[ch][CHANNEL_MAPPINGS_GPIO_PIN_INDEX];
            value = microkit_mr_get(REQ_GPIO_VALUE_SLOT);
            return handle_set_gpio_request(pin, config, value);
        case SET_IRQ:
            if (count != 2) {
                return invalid_request_error_message(INVALID_NUM_ARGS);
            }
            // check mapping
            if (cli_channel_mappings[ch][CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX] < 0) {
                return invalid_request_error_message(INVALID_CONFIG_ENTRY);
            }
            config = microkit_mr_get(REQ_GPIO_CONFIG_SLOT);
            meson_channel = cli_channel_mappings[ch][CHANNEL_MAPPINGS_DEV_IRQ_CHANNEL_INDEX] - DEV_IRQ_CHANNEL_OFFSET;
            value = microkit_mr_get(REQ_GPIO_VALUE_SLOT);
            return handle_set_irq_request(meson_channel, config, value);
        default:
            return invalid_request_error_message(INVALID_LABEL);
    }
}
