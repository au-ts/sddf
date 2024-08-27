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
#define LOG_VIRTUALISER(...) do{ sddf_dprintf("I2C VIRTUALISER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRTUALISER(...) do{}while(0)
#endif

#define LOG_VIRTUALISER_ERR(...) do{ sddf_printf("I2C VIRTUALISER|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define BUS_UNCLAIMED (-1)

/*
 * Note that we have a fundamental assumption that the regions of memory for a
 * client are indexed the same as the channel number. E.g the first client
 * request region virtual address is channel number 0.
 * We believe this restriction should not be too restrictive, but we will see
 * what happens...
 */

#define NUM_CLIENTS 2
#define DRIVER_CH 2

#if DRIVER_CH < NUM_CLIENTS
#error "DRIVER_CH must be higher than client channels"
#endif

uintptr_t driver_data_offsets[NUM_CLIENTS] = { 0, 0x1000 }; // change if NUM_CLIENTS changes
size_t client_data_sizes[NUM_CLIENTS] = { 0x1000, 0x1000 }; // change if NUM_CLIENTS changes

i2c_queue_handle_t client_queues[NUM_CLIENTS];
i2c_queue_handle_t driver_queue;

uintptr_t client_request_regions[NUM_CLIENTS] = { 0x4000000, 0x4001000 }; // change if NUM_CLIENTS changes
uintptr_t client_response_regions[NUM_CLIENTS] = { 0x5000000, 0x5001000 }; // change if NUM_CLIENTS changes

// Security list: owner of each i2c address on the bus
int security_list[I2C_BUS_ADDRESS_MAX + 1];

uintptr_t driver_response_region; // mapped memory
uintptr_t driver_request_region; // mapped memory

void process_request(microkit_channel ch)
{
    bool enqueued = false;
    assert(ch < NUM_CLIENTS);

    /* Do not process the request if we cannot pass it to the driver */
    while (!i2c_queue_empty(client_queues[ch].request) && !i2c_queue_full(driver_queue.request)) {
        size_t offset = 0;
        size_t bus_address = 0;
        unsigned int len = 0;
        int err = i2c_dequeue_request(client_queues[ch], &bus_address, &offset, &len);
        if (err) {
            LOG_VIRTUALISER_ERR("could not dequeue from request queue\n");
            return;
        }

        // Check that client can actually access bus
        if (bus_address > I2C_BUS_ADDRESS_MAX || security_list[bus_address] != ch) {
            LOG_VIRTUALISER_ERR("invalid bus address (0x%lx) requested by client 0x%x\n", bus_address, ch);
            continue;
        }

        if (offset > client_data_sizes[ch]) {
            LOG_VIRTUALISER_ERR("invalid offset (0x%lx) given by client 0x%x. Max offset is 0x%lx\n", offset, ch,
                                client_data_sizes[ch]);
            continue;
        }

        // Now we need to convert the offset into an offset the driver can use in its address space.
        size_t driver_offset = driver_data_offsets[ch] + offset;
        err = i2c_enqueue_request(driver_queue, bus_address, driver_offset, len);
        /* If this assert fails we have a race as the driver should only ever be dequeuing */
        assert(!err);

        enqueued = true;
    }

    if (enqueued) {
        microkit_deferred_notify(DRIVER_CH);
    }
}

void process_response()
{
    /*
     * Process all responses that the driver has queued up. We look at which client currently has the
     * claim on the bus and deliver the response to them. If a client's response queue is full we
     * simply drop the response (a typical client will never reach that scenario unless it has some
     * catastrophic bug or is malicious).
     */
    while (!i2c_queue_empty(driver_queue.response)) {
        size_t bus_address = 0;
        size_t driver_offset = 0;
        unsigned int len = 0;

        /* We trust the driver to give us a sane bus address */
        int err = i2c_dequeue_response(driver_queue, &bus_address, &driver_offset, &len);
        /* If this assert fails we have a race as the virtualiser should be the only one dequeuing
         * from the driver's response queue */
        assert(!err);

        size_t ch = security_list[bus_address];
        if (ch == BUS_UNCLAIMED) {
            /* The client has released the bus before receiving all their responses, so we simply
             * drop the response. */
            continue;
        }

        size_t client_offset = driver_offset - driver_data_offsets[ch];
        /* There is no point checking if the enqueue succeeds or not. */
        i2c_enqueue_response(client_queues[ch], bus_address, client_offset, len);

        microkit_notify(ch);
    }
}

void init(void)
{
    LOG_VIRTUALISER("initialising\n");
    for (int i = 0; i < I2C_BUS_ADDRESS_MAX + 1; i++) {
        security_list[i] = BUS_UNCLAIMED;
    }
    driver_queue = i2c_queue_init((i2c_queue_t *) driver_request_region, (i2c_queue_t *) driver_response_region);
    for (int i = 0; i < NUM_CLIENTS; i++) {
        client_queues[i] = i2c_queue_init((i2c_queue_t *) client_request_regions[i],
                                          (i2c_queue_t *) client_response_regions[i]);
    }
}

void notified(microkit_channel ch)
{
    if (ch == DRIVER_CH) {
        process_response();
    } else {
        process_request(ch);
    }
}

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t bus = microkit_mr_get(I2C_BUS_SLOT);

    if (label != I2C_BUS_CLAIM && label != I2C_BUS_RELEASE) {
        LOG_VIRTUALISER_ERR("unknown label (0x%lx) given by client on channel 0x%x\n", label, ch);
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    if (bus > I2C_BUS_ADDRESS_MAX) {
        LOG_VIRTUALISER_ERR("invalid bus address (0x%lx) given by client on "
                            "channel 0x%x. Max bus address is 0x%x\n", bus, ch, I2C_BUS_ADDRESS_MAX);
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    switch (label) {
    case I2C_BUS_CLAIM:
        // We have a valid bus address, we need to make sure no one else has claimed it.
        if (security_list[bus] != BUS_UNCLAIMED) {
            LOG_VIRTUALISER_ERR("bus address 0x%lx already claimed, cannot claim for channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(I2C_FAILURE, 0);
        }

        security_list[bus] = ch;
        break;
    case I2C_BUS_RELEASE:
        if (security_list[bus] != ch) {
            LOG_VIRTUALISER_ERR("bus address 0x%lx is not claimed by channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(I2C_FAILURE, 0);
        }

        security_list[bus] = BUS_UNCLAIMED;
        break;
    default:
        LOG_VIRTUALISER_ERR("reached unreachable case\n");
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    return microkit_msginfo_new(I2C_SUCCESS, 0);
}
