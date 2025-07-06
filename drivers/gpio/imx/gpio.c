/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>
#include <sddf/util/fence.h>
#include <sddf/gpio/protocol.h>
#include <gpio_config.h>
#include "gpio.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

volatile imx_gpio_regs_t *gpio_regs;

// For O(1) lookups
static int pin_subscriber[PINS_PER_BANK] = {-1};

uint32_t craft_error_label(gpio_error_t error_code) {
    uint32_t e = error_code | BIT(SDDF_GPIO_RESPONSE_ERROR_BIT);
    return e;
}

// NOTE: there is actual some single line ones that the manual mentions however
// From my research they dont appear to leave the GPIO block to go to the GIC
// Also Linux doesn't use them and you dont need them anyway because we can just use the combined lines.
void notified(microkit_channel ch)
{
    if (ch == device_resources.irqs[0].id ||
    	ch == device_resources.irqs[1].id) 
    {
		uint32_t clear_mask = 0;

      	for (int pin = 0; pin < PINS_PER_BANK; pin++) {
      		// 1. Check status reg
      		if (gpio_regs->isr & BIT(pin)) {
      			// 2. Clear if set
      			clear_mask |= BIT(pin);

      			// 3. Notify client
      			microkit_notify(pin_subscriber[pin]);
      		}
      	}

      	gpio_regs->isr &= ~clear_mask;

      	// We want it to be cleared before the microkit acknowledges
      	THREAD_MEMORY_ACQUIRE();

      	microkit_deferred_irq_ack(ch);
    } 
    else {
        sddf_dprintf("GPIO DRIVER|LOG: unexpected notification from channel %u\n", ch);
        return;
    }
}

static inline seL4_MessageInfo_t set(int pin, uint32_t value) {
	if (value) {
		gpio_regs->dr |= BIT(pin);
	} 
	else {
		gpio_regs->dr &= ~BIT(pin);
	}

	return microkit_msginfo_new(0, 0);
}

static inline seL4_MessageInfo_t get(int pin) {
	// The dr register can be used to read line value for both directions
    uint32_t value = (gpio_regs->dr >> pin) & BIT(0);

    return microkit_msginfo_new(value, 0);
}

static inline seL4_MessageInfo_t set_direction_output(int pin, uint32_t value) {
    // Write value first then flip direction
    if (value) {
	    gpio_regs->dr |= BIT(pin);
    }
	else {
	    gpio_regs->dr &= ~BIT(pin);
	}
	gpio_regs->gdir |= BIT(pin);

	return microkit_msginfo_new(0, 0);
}

static inline seL4_MessageInfo_t set_direction_input(int pin) {
    gpio_regs->gdir &= ~BIT(pin);

    return microkit_msginfo_new(0, 0);
}

static inline seL4_MessageInfo_t get_direction(int pin) {
    uint32_t dir = (gpio_regs->gdir >> pin) & BIT(0);

    return microkit_msginfo_new(dir, 0);
}

static inline seL4_MessageInfo_t set_config(int pin, uint32_t value, uint32_t argument) {
    return microkit_msginfo_new(craft_error_label(SDDF_GPIO_EOPNOTSUPP), 0);
}

static inline seL4_MessageInfo_t irq_enable(int pin) {
    gpio_regs->imr |= BIT(pin);

    // TODO: should we flush? Because we could recieve an irq in the meantime after this.

    return microkit_msginfo_new(0, 0);
}

static inline seL4_MessageInfo_t irq_disable(int pin) {
    gpio_regs->imr &= ~BIT(pin);

     // TODO: should we flush? Because we could recieve an irq in the meantime after this.

    return microkit_msginfo_new(0, 0);
}

static inline seL4_MessageInfo_t irq_set_type(int pin, uint32_t type) {
    uint32_t shift = (pin % 16) * 2;
    uint32_t icr_val = ICR_LOW_LEVEL;
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
        return microkit_msginfo_new(craft_error_label(SDDF_GPIO_EINVAL), 0);
    }

    if (pin < 16) {
        gpio_regs->icr1 = (gpio_regs->icr1 & ~(0x3u << shift)) | (icr_val << shift);
    }
    else {
        gpio_regs->icr2 = (gpio_regs->icr2 & ~(0x3u << shift)) | (icr_val << shift);
    }

    if (both) {
        gpio_regs->edge_sel |= BIT(pin);
    }
    else {
        gpio_regs->edge_sel &= ~BIT(pin);
    }

    return microkit_msginfo_new(0, 0); 
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    sddf_dprintf("GPIO DRIVER|LOG: ppc notification from channel %u\n", ch);

    // Parse the label
    uint32_t label = microkit_msginfo_get_label(msginfo);
    uint32_t interface_function = label & SDDF_REQUEST_INTERFACE_MASK;
    uint32_t value = label & GPIO_REQUEST_VALUE_MASK;

    // Check what pin it has
    int pin = gpio_driver_channel_mappings[ch].pin;

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
        uint32_t arguement = seL4_GetMR(0);
        return set_config(pin, value, arguement);
    }
    case SDDF_GPIO_IRQ_ENABLE: {
        return irq_enable(pin);
    }
    case SDDF_GPIO_IRQ_DISABLE: {
        return irq_disable(pin);
    }
    case SDDF_GPIO_IRQ_SET_TYPE: {
        return irq_set_type(pin, value);
    }
    default:
        sddf_dprintf("GPIO DRIVER|LOG: Unknown request %lu to gpio from channel %u\n", microkit_msginfo_get_label(msginfo),
                     ch);
        return microkit_msginfo_new(craft_error_label(SDDF_GPIO_EOPNOTSUPP), 0);
    }
}

void validate_gpio_config() {
	for (int ch = 0; ch < MICROKIT_MAX_CHANNELS; ch++) {
        int pin = gpio_driver_channel_mappings[ch].pin;
        int irq = gpio_driver_channel_mappings[ch].irq;

        // Irq without pin check
        if (pin < 0 && irq >= 0) {
        	sddf_dprintf("GPIO DRIVER|ERROR: Pin must be set if IRQ is set! (ch=%d, irq=%d)", ch, irq);
        	while (1) {}
        }

    	// Nothing to configure
        if (pin < 0) {
            continue;
        }

        // Check a client hasn't claimed the channels we use for device interrupts 
		if (device_resources.irqs[0].id == ch) {
			sddf_dprintf("GPIO DRIVER|ERROR: Client can't claim channel used for device irqs : %d", ch);
        	while (1) {}
		} else if (device_resources.irqs[1].id == ch) {
			sddf_dprintf("GPIO DRIVER|ERROR: Client can't claim channel used for device irqs : %d", ch);
        	while (1) {}
		}

        // Check pin is valid number
        if (pin >= PINS_PER_BANK) {
        	sddf_dprintf("GPIO DRIVER|ERROR: Invalid pin number : %d", pin);
        	while (1) {}
        }

       	// Unique-pin check
        int seen = 0;
        for (int ch_2 = 0; ch_2 < MICROKIT_MAX_CHANNELS; ch_2++) {
            if (gpio_driver_channel_mappings[ch_2].pin == pin) {
                seen++;
            }
        }
        if (seen != 1) {
            sddf_dprintf("GPIO DRIVER|ERROR: pin %d mapped %d times (must be exactly once)", pin, seen);
        	while (1) {}
        } 

    	if (irq < 0) {
            continue;
        }

        // For fast lookups in notify
        pin_subscriber[pin] = ch;

        // Since we can only bind each pin to one designated interrupt we dont validate the irq picked
        // Other then it being above 0
      }
}

void disable_all_interrupts() {
	gpio_regs->imr = 0;	
	gpio_regs->isr = ~0;	


	// Flush to make sure we go NO more interrupts
	THREAD_MEMORY_ACQUIRE();

	microkit_irq_ack(device_resources.irqs[0].id);
	microkit_irq_ack(device_resources.irqs[1].id);
}

void init(void)
{
	assert(device_resources_check_magic(&device_resources));

    assert(device_resources.num_irqs == 2);
    assert(device_resources.num_regions == 1);

    // TODO: make sure thres no offset
    gpio_regs = (imx_gpio_regs_t *)device_resources.regions[0].region.vaddr;

    validate_gpio_config();

    disable_all_interrupts();
}
