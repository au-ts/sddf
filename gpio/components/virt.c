/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #define DEBUG_VIRTUALISER

#ifdef DEBUG_VIRTUALISER
#define LOG_VIRTUALISER(...) do{ sddf_dprintf("GPIO VIRTUALISER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRTUALISER(...) do{}while(0)
#endif

#define LOG_VIRTUALISER_ERR(...) do{ sddf_printf("GPIO VIRTUALISER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

/*
 * Note that we have a fundamental assumption that the regions of memory for a
 * client are indexed the same as the channel number. E.g the first client
 * notification region virtual address is channel number 0.
 * We believe this restriction should not be too restrictive, but we will see
 * what happens...
 */

#define NUM_CLIENTS 1
#define DRIVER_CH 1

#if DRIVER_CH < NUM_CLIENTS
#error "DRIVER_CH must be higher than client channels"
#endif

gpio_irq_queue_handle_t client_queues[NUM_CLIENTS];
gpio_irq_queue_handle_t driver_queue;

uintptr_t driver_notification_data_region; // mapped memory

uintptr_t client_notification_data_regions[NUM_CLIENTS] = { 0x5000000 }; // change if NUM_CLIENTS changes

#define UNCLAIMED (-1)

int gpio_security_list[GPIO_PIN_COUNT];
int irq_security_list[IRQ_CHANNEL_COUNT];

static void forward_notification() {
    /*
     * Process all responses that the driver has queued up. We look at which client currently has the
     * claim on the GPIO channel (we assume this was initially done correctly by the driver)
     * and forward the IRQ to them. If a client's response queue is full we
     * simply drop the response (a typical client will never reach that scenario unless it has some
     * catastrophic bug or is malicious).
     */
    // while (!i2c_queue_empty(driver_queue.notfications)) {
    //     uint8_t channel_id;
    //     /* We trust the driver to give us a sane channel_id */
    //     int err = i2c_dequeue_response(driver_queue, &bus_address, &driver_offset, &len);
    //     /* If this assert fails we have a race as the virtualiser should be the only one dequeuing
    //      * from the driver's response queue */
    //     assert(!err);




    // }

}

static seL4_MessageInfo_t handle_gpio_config_request(microkit_channel ch, seL4_MessageInfo_t msginfo) {
    if (microkit_msginfo_get_count(msginfo) == 0) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_NUM_ARGS);
        return error_message;
    }
    size_t pin = microkit_mr_get(REQ_GPIO_PIN_SLOT);
    if (pin > GPIO_PIN_COUNT) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN);
        return error_message;
    }

    if (gpio_security_list[pin] != ch) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PERMISSION);
        return error_message;
    }

    // forward request to driver and return back to client
    return microkit_ppcall(DRIVER_CH, msginfo);
}

static seL4_MessageInfo_t handle_gpio_pin_claim(int client_id, size_t pin) {
    if (pin > GPIO_PIN_COUNT) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN);
        return error_message;
    }

    if (pin == 0) {
        LOG_VIRTUALISER_ERR("We use this as the UNASSIGNED_IRQ_GPIO_PIN_VALUE so for security reasons it cannot be claimed!\n");
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN);
        return error_message;
    }

    if (gpio_security_list[pin] != UNCLAIMED) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN_ALREADY_CLAIMED);
        return error_message;
    }

    gpio_security_list[pin] = client_id;

    return microkit_msginfo_new(SUCCESS, 0);
}

static seL4_MessageInfo_t handle_gpio_pin_release(int client_id, size_t pin) {
    if (pin > GPIO_PIN_COUNT) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN);
        return error_message;
    }

    if (gpio_security_list[pin] == UNCLAIMED || gpio_security_list[pin] == client_id) {
        gpio_security_list[pin] = UNCLAIMED;
        return microkit_msginfo_new(SUCCESS, 0);
    }

    seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
    microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PERMISSION);
    return error_message;
}

static seL4_MessageInfo_t handle_irq_config_request(microkit_channel ch, seL4_MessageInfo_t msginfo) {
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t count = microkit_msginfo_get_count(msginfo);
    if (label == GET_IRQ_CONFIG && count != 0) {
        size_t channel = microkit_mr_get(REQ_IRQ_CHANNEL_SLOT);
        if (channel > IRQ_CHANNEL_COUNT) {
            seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
            microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_CHANNEL);
            return error_message;
        }
        if (irq_security_list[channel] != ch) {
            seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
            microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PERMISSION);
            return error_message;
        }
    } else { // SET_IRQ_CONFIG
        if (count < 3) {
            return invalid_request_error_message(INVALID_NUM_ARGS);
        }
        size_t channel = microkit_mr_get(REQ_IRQ_CHANNEL_SLOT);
        size_t config = microkit_mr_get(REQ_IRQ_CONFIG_SLOT);
        if (channel > IRQ_CHANNEL_COUNT) {
            seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
            microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_CHANNEL);
            return error_message;
        }
        if (irq_security_list[channel] != ch) {
            seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
            microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PERMISSION);
            return error_message;
        }

        // check the client has permissions for the pin as well
        if (config == PIN) {
            size_t value = microkit_mr_get(REQ_GPIO_VALUE_SLOT);
            // check secuirty list of gpio stuff
            if (pin > GPIO_PIN_COUNT) {
                seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
                microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN);
                return error_message;
            }

            if (gpio_security_list[pin] != ch) {
                seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
                microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PERMISSION);
                return error_message;
            }
        }

    }

    // valid , forward to driver
    return microkit_ppcall(DRIVER_CH, msginfo);
}

static seL4_MessageInfo_t handle_irq_channel_claim(int client_id, size_t channel) {
    if (channel > IRQ_CHANNEL_COUNT) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_CHANNEL);
        return error_message;
    }

    if (irq_security_list[channel] != UNCLAIMED) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PIN_ALREADY_CLAIMED);
        return error_message;
    }

    irq_security_list[channel] = client_id;

    return microkit_msginfo_new(SUCCESS, 0);
}

static seL4_MessageInfo_t handle_irq_channel_release(int client_id, size_t channel) {
    if (channel > IRQ_CHANNEL_COUNT) {
        seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
        microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_CHANNEL);
        return error_message;
    }

    if (irq_security_list[channel] == UNCLAIMED) {
        irq_security_list[channel] = UNCLAIMED;
        return microkit_msginfo_new(SUCCESS, 0);
    }

    if (irq_security_list[channel] == client_id) {
        // reset the configured channel in the virtualiser to the default value for no configured pin in the channel
        // TODO




    }

    seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
    microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_PERMISSION);
    return error_message;
}


void init(void)
{
    LOG_VIRTUALISER("initialising\n");
    for (int i = 0; i < GPIO_PIN_COUNT + 1; i++) {
        gpio_security_list[i] = UNCLAIMED;
    }
    for (int i = 0; i < IRQ_CHANNEL_COUNT + 1; i++) {
        irq_security_list[i] = UNCLAIMED;
    }
    driver_queue = gpio_irq_queue_init((gpio_irq_queue_t *) driver_notification_data_region);
    for (int i = 0; i < NUM_CLIENTS; i++) {
        client_queues[i] = gpio_irq_queue_init((gpio_irq_queue_t *) client_notification_data_regions[i]);
    }
}

void notified(microkit_channel ch)
{
    if (ch == DRIVER_CH) {
        forward_notification();
    } else {
        microkit_dbg_puts("DRIVER|ERROR: unexpected notification!\n");
    }
}

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t count = microkit_msginfo_get_count(msginfo);

    switch (label) {
        case GET_GPIO_CONFIG:
            return handle_gpio_config_request(ch, msginfo);
        case SET_GPIO_CONFIG:
            return handle_gpio_config_request(ch, msginfo);
        case GET_IRQ_CONFIG:
            return handle_irq_config_request(ch, msginfo);
        case SET_IRQ_CONFIG:
            return handle_irq_config_request(ch, msginfo);
        case GPIO_PIN_CLAIM:
            if (count != 1) {
                seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
                microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_NUM_ARGS);
                return error_message;
            }
            size_t pin = microkit_mr_get(REQ_GPIO_PIN_SLOT);
            return handle_gpio_pin_claim(ch, pin);
        case GPIO_PIN_RELEASE:
            if (count != 1) {
                seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
                microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_NUM_ARGS);
                return error_message;
            }
            size_t pin = microkit_mr_get(REQ_GPIO_PIN_SLOT);
            return handle_gpio_pin_release(ch, pin);
        case IRQ_CHANNEL_CLAIM:
            if (count != 1) {
                seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
                microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_NUM_ARGS);
                return error_message;
            }
            size_t channel = microkit_mr_get(REQ_IRQ_CHANNEL_SLOT);
            return handle_irq_channel_claim(ch, channel);
        case IRQ_CHANNEL_RELEASE:
            if (count != 1) {
                seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
                microkit_mr_set(RES_GPIO_IRQ_ERROR_SLOT, INVALID_NUM_ARGS);
                return error_message;
            }
            size_t channel = microkit_mr_get(REQ_IRQ_CHANNEL_SLOT);
            return handle_irq_channel_release(ch, channel);
        default:
            seL4_MessageInfo_t error_message = microkit_msginfo_new(FAILURE, 1);
            microkit_mr_set(RES_GPIO_ERROR_SLOT, INVALID_LABEL);
            return error_message;
    }
}
