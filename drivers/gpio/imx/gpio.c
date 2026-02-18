/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/gpio/protocol.h>
#include <gpio_config.h>
#include "gpio.h"

// #define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_DRIVER(...) do{ sddf_dprintf("GPIO DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_DRIVER(...) do{}while(0)
#endif

#define LOG_DRIVER_ERR(...) do{ sddf_printf("GPIO DRIVER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

volatile imx_gpio_regs_t *gpio_regs;

/* Map pin to client channels */
static int pin_subscriber[PINS_PER_BANK];

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

static inline void init_pin_subscribers()
{
    for (int i = 0; i < PINS_PER_BANK; ++i) {
        pin_subscriber[i] = -1;
    }
}

static void print_irq_pin_subscribers()
{
    LOG_DRIVER("IRQ Pin Subscribers:\n");

    for (int i = 0; i < PINS_PER_BANK; ++i) {
        if (pin_subscriber[i] != -1) {
            LOG_DRIVER("Pin %d -> Subscriber %d\n", i, pin_subscriber[i]);
        }
    }
}

static inline microkit_msginfo error_response(gpio_error_t error_code)
{
    uint32_t e = error_code | BIT(SDDF_GPIO_RESPONSE_ERROR_BIT);
    return microkit_msginfo_new(e, 0);
}

static inline bool check_irq_permission(microkit_channel ch)
{
    return gpio_driver_channel_mappings[ch].irq > 0;
}

static void handle_gpio_irq(int ch, int start_pin, int end_pin)
{
    uint32_t clear_mask = 0;

    /* Go through pin and build up a mask of IRQs to clear. */
    for (int pin = start_pin; pin < end_pin; pin++) {
        /* If the pin is unmasked and the IRQ was related to this pin, add it to the mask and notify
             * the client subscribed to that pin. */
        if ((gpio_regs->imr & BIT(pin)) && (gpio_regs->isr & BIT(pin))) {
            clear_mask |= BIT(pin);
            microkit_notify(pin_subscriber[pin]);
        }
    }

    gpio_regs->imr &= ~clear_mask;

    // We want it to be cleared before the microkit acknowledges so we don't enter notified again.
    microkit_deferred_irq_ack(ch);
}

void notified(microkit_channel ch)
{
    /*
     * We have two potential interrupts to deal with, one for the lower 16 pins, and another for the
     * the upper 16 pins.
     * There exists single interrupt lines for the device, however they do not appear to leave the GPIO
     * block and go the interrupt controller, so we do not make use of them. It seems that Linux does
     * not either.
     */
    if (ch == device_resources.irqs[0].id) {
        handle_gpio_irq(ch, 0, PINS_PER_BANK / 2);
    } else if (ch == device_resources.irqs[1].id) {
        handle_gpio_irq(ch, PINS_PER_BANK / 2, PINS_PER_BANK);
    } else {
        LOG_DRIVER("unexpected notification from channel %u\n", ch);
    }
}

static inline microkit_msginfo set(int pin, uint32_t value)
{
    if (value) {
        gpio_regs->dr |= BIT(pin);
    } else {
        gpio_regs->dr &= ~BIT(pin);
    }

    return microkit_msginfo_new(0, 0);
}

static inline microkit_msginfo get(int pin)
{
    uint32_t value = (gpio_regs->psr >> pin) & BIT(0);

    return microkit_msginfo_new(value, 0);
}

static inline microkit_msginfo set_direction_output(int pin, uint32_t value)
{
    if (value) {
        gpio_regs->dr |= BIT(pin);
    } else {
        gpio_regs->dr &= ~BIT(pin);
    }

    // This instruction already reads back to ensure previous instructions completion
    gpio_regs->gdir |= BIT(pin);

    return microkit_msginfo_new(0, 0);
}

static inline microkit_msginfo set_direction_input(int pin)
{
    gpio_regs->gdir &= ~BIT(pin);

    return microkit_msginfo_new(0, 0);
}

static inline microkit_msginfo get_direction(int pin)
{
    uint32_t dir = (gpio_regs->gdir >> pin) & BIT(0);

    return microkit_msginfo_new(dir, 0);
}

static inline microkit_msginfo set_config(int pin, uint32_t value, uint32_t argument)
{
    return error_response(SDDF_GPIO_EOPNOTSUPP);
}

static inline microkit_msginfo irq_enable(int pin)
{
    // Clear all noise that happened before the interrupt started
    gpio_regs->isr = BIT(pin);
    // This instruction already reads back to ensure previous instructions completion
    gpio_regs->imr |= BIT(pin);

    return microkit_msginfo_new(0, 0);
}

// The semantic of disable also means unchecking the status register
static inline microkit_msginfo irq_disable(int pin)
{
    gpio_regs->imr &= ~BIT(pin);

    // Since it's the same peripheral a read back will mean it completes
    (void)gpio_regs->imr;

    // Now that we have unmasked we uncheck the status register
    // so that if we go to notified we don't process this irq if
    // it was set before we unmasked

    gpio_regs->isr = BIT(pin);

    return microkit_msginfo_new(0, 0);
}

static inline microkit_msginfo irq_set_type(int pin, uint32_t type)
{
    uint32_t shift = (pin % 16) * 2;
    uint32_t icr_val = (pin < 16) ? ((gpio_regs->icr1 >> shift) & 0x3u) : ((gpio_regs->icr2 >> shift) & 0x3u);

    bool both = false;

    switch (type) {
    case SDDF_IRQ_TYPE_EDGE_RISING:
        icr_val = ICR_RISING_EDGE;
        break;
    case SDDF_IRQ_TYPE_EDGE_FALLING:
        icr_val = ICR_FALLING_EDGE;
        break;
    case SDDF_IRQ_TYPE_LEVEL_HIGH:
        icr_val = ICR_HIGH_LEVEL;
        break;
    case SDDF_IRQ_TYPE_LEVEL_LOW:
        icr_val = ICR_LOW_LEVEL;
        break;
    case SDDF_IRQ_TYPE_EDGE_BOTH:
        both = true;
        break;
    default:
        return error_response(SDDF_GPIO_EINVAL);
    }

    if (pin < 16) {
        gpio_regs->icr1 = (gpio_regs->icr1 & ~(0x3u << shift)) | (icr_val << shift);
    } else {
        gpio_regs->icr2 = (gpio_regs->icr2 & ~(0x3u << shift)) | (icr_val << shift);
    }

    // These instructions already read back to ensure previous instructions completion
    if (both) {
        gpio_regs->edge_sel |= BIT(pin);
    } else {
        gpio_regs->edge_sel &= ~BIT(pin);
    }

    return microkit_msginfo_new(0, 0);
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    uint32_t label = microkit_msginfo_get_label(msginfo);
    uint32_t interface_function = label & SDDF_REQUEST_INTERFACE_MASK;
    uint32_t value = gpio_decode_value(label);

    // Check what pin it has
    int pin = gpio_driver_channel_mappings[ch].pin;

    // Unexpected channel
    if (pin < 0) {
        return error_response(SDDF_GPIO_EPERM);
    }

    switch (interface_function) {
    case SDDF_GPIO_SET: {
        return set(pin, value);
    }
    case SDDF_GPIO_GET: {
        return get(pin);
    }
    case SDDF_GPIO_DIRECTION_OUTPUT: {
        return set_direction_output(pin, value);
    }
    case SDDF_GPIO_DIRECTION_INPUT: {
        return set_direction_input(pin);
    }
    case SDDF_GPIO_GET_DIRECTION: {
        return get_direction(pin);
    }
    case SDDF_GPIO_SET_CONFIG: {
        uint32_t argument = microkit_mr_get(0);
        return set_config(pin, value, argument);
    }
    case SDDF_GPIO_IRQ_ENABLE: {
        if (check_irq_permission(ch)) {
            return irq_enable(pin);
        }
        return error_response(SDDF_GPIO_EPERM);
    }
    case SDDF_GPIO_IRQ_DISABLE: {
        if (check_irq_permission(ch)) {
            return irq_disable(pin);
        }
        return error_response(SDDF_GPIO_EPERM);
    }
    case SDDF_GPIO_IRQ_SET_TYPE: {
        if (check_irq_permission(ch)) {
            return irq_set_type(pin, value);
        }
        return error_response(SDDF_GPIO_EPERM);
    }
    default:
        LOG_DRIVER("Unknown request %lu to gpio from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        return error_response(SDDF_GPIO_EOPNOTSUPP);
    }
}

void validate_gpio_config()
{
    for (int ch = 0; ch < MICROKIT_MAX_CHANNELS; ch++) {
        int pin = gpio_driver_channel_mappings[ch].pin;
        int irq = gpio_driver_channel_mappings[ch].irq;

        // Irq without pin check
        if (pin < 0 && irq >= 0) {
            LOG_DRIVER_ERR("Pin must be set if IRQ is set! (ch=%d, irq=%d)\n", ch, irq);
            assert(false);
        }

        // Nothing to configure
        if (pin < 0) {
            continue;
        }

        // Check a client hasn't claimed the channels we use for device interrupts
        if (device_resources.irqs[0].id == ch) {
            LOG_DRIVER_ERR("Client can't claim channel used for device irqs : %d\n", ch);
            assert(false);
        } else if (device_resources.irqs[1].id == ch) {
            LOG_DRIVER_ERR("Client can't claim channel used for device irqs : %d\n", ch);
            assert(false);
        }

        // Check pin is valid number
        if (pin >= PINS_PER_BANK) {
            LOG_DRIVER_ERR("Invalid pin number : %d\n", pin);
            assert(false);
        }

        // Unique-pin check
        int seen = 0;
        for (int ch_2 = 0; ch_2 < MICROKIT_MAX_CHANNELS; ch_2++) {
            if (gpio_driver_channel_mappings[ch_2].pin == pin) {
                seen++;
            }
        }
        if (seen != 1) {
            LOG_DRIVER_ERR("pin %d mapped %d times (must be exactly once)\n", pin, seen);
            assert(false);
        }

        if (irq < 0) {
            continue;
        }

        // For fast lookups in notify
        pin_subscriber[pin] = ch;

        // Since we can only bind each pin to one designated interrupt we don't validate the irq picked
        // Other then it being above 0
    }
}

void disable_all_interrupts()
{
    gpio_regs->imr = 0;

    microkit_irq_ack(device_resources.irqs[0].id);
    microkit_irq_ack(device_resources.irqs[1].id);
}

void init(void)
{
    LOG_DRIVER("Starting.\n");

    assert(device_resources_check_magic(&device_resources));

    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    gpio_regs = (imx_gpio_regs_t *)device_resources.regions[0].region.vaddr;

    init_pin_subscribers();

    validate_gpio_config();

    disable_all_interrupts();

    print_irq_pin_subscribers();

    LOG_DRIVER("Finished.\n");
}
