/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>
#include <sddf/i2c/config.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #define DEBUG_VIRT

#ifdef DEBUG_VIRT
#define LOG_VIRT(...) do{ sddf_dprintf("I2C VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRT(...) do{}while(0)
#endif

#define LOG_VIRT_ERR(...) do{ sddf_printf("I2C VIRT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define BUS_UNCLAIMED (-1)

#define CLIENT_CH_OFFSET 1

__attribute__((__section__(".i2c_virt_config"))) i2c_virt_config_t config;

i2c_queue_handle_t client_queues[SDDF_I2C_MAX_CLIENTS];
i2c_queue_handle_t driver_queue;

// Security list: owner of each i2c address on the bus
int security_list[I2C_BUS_ADDRESS_MAX + 1];

void process_request(uint32_t client_id)
{
    bool enqueued = false;
    assert(client_id < config.num_clients);

    /* Do not process the request if we cannot pass it to the driver */
    while (!i2c_queue_empty(client_queues[client_id].request->ctrl) && !i2c_queue_full(driver_queue.request->ctrl)) {
        i2c_addr_t bus_address = 0;
        uintptr_t data_start_vaddr;
        uintptr_t meta_base_vaddr;
        uint16_t len;
        int err = i2c_dequeue_request(client_queues[client_id], &bus_address, &data_start_vaddr, &meta_base_vaddr,
                                      &len);
        if (err) {
            LOG_VIRT_ERR("could not dequeue from request queue\n");
            return;
        }

        // Check that client can actually access bus
        if (bus_address > I2C_BUS_ADDRESS_MAX || security_list[bus_address] != client_id) {
            LOG_VIRT_ERR("invalid bus address (0x%x) requested by client 0x%x\n", bus_address, client_id);
            continue;
        }
        LOG_VIRT("Request: bus address = %u : data = %p : len = %u\n", bus_address, (void *)data_start_vaddr, len);
        LOG_VIRT("Data origin for this client: %p\n", (void *)config.clients[client_id].client_data_vaddr);

        size_t offset = (size_t)data_start_vaddr - (size_t)config.clients[client_id].client_data_vaddr;
        LOG_VIRT("request offset: %zu\n", offset);
        if (offset > config.clients[client_id].data_size
            || data_start_vaddr > config.clients[client_id].driver_data_vaddr) {
            LOG_VIRT_ERR("invalid data vaddr (0x%lx) given by client %u.", data_start_vaddr, client_id);
            continue;
        }

        // Now we need to convert the offset into an offset the driver can use in its address space.
        uintptr_t driver_data_vaddr = (uintptr_t)(config.clients[client_id].driver_data_vaddr + offset);

        // We replace the meta base of the client with the driver's base. The client doesn't need
        // to supply one at all!
        LOG_VIRT("Enqueueing request to driver...\n");
        err = i2c_enqueue_request(driver_queue, bus_address, driver_data_vaddr,
                                  config.clients[client_id].driver_meta_vaddr, len);
        /* If this assert fails we have a race as the driver should only ever be dequeuing */
        assert(!err);

        enqueued = true;
    }

    if (enqueued) {
        LOG_VIRT("Firing deferred notify to driver...\n");
        microkit_deferred_notify(config.driver.id);
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
    LOG_VIRT("PROCESS RESPONSE\n");
    while (!i2c_queue_empty(driver_queue.response->ctrl)) {
        LOG_VIRT("Handling response...\n");
        i2c_addr_t bus_address = 0;
        i2c_err_t error = 0;
        size_t err_cmd = 0;

        /* We trust the driver to give us a sane bus address */
        int err = i2c_dequeue_response(driver_queue, &bus_address, &error, &err_cmd);
        /* If this assert fails we have a race as the virtualiser should be the only one dequeuing
         * from the driver's response queue */
        assert(!err);

        size_t client_id = security_list[bus_address];
        if (client_id == BUS_UNCLAIMED) {
            LOG_VIRT_ERR("Driver response belongs to no authenticated client!\n");
            /* The client has released the bus before receiving all their responses, so we simply
             * drop the response. */
            continue;
        }

        /* There is no point checking if the enqueue succeeds or not. */
        int ret = i2c_enqueue_response(client_queues[client_id], bus_address, error, err_cmd);

        LOG_VIRT("Notifying client.\n");
        microkit_notify(CLIENT_CH_OFFSET + client_id);
    }
}

void init(void)
{
    assert(i2c_config_check_magic(&config));
    assert(config.driver.id == 0);  // @leslr: is this needed? sdfgen should remove any need
    LOG_VIRT("initialising\n");
    for (int i = 0; i < I2C_BUS_ADDRESS_MAX + 1; i++) {
        security_list[i] = BUS_UNCLAIMED;
    }
    driver_queue = i2c_queue_init(config.driver.req_queue.vaddr, config.driver.resp_queue.vaddr);
    for (int i = 0; i < config.num_clients; i++) {
        /*LOG_VIRT("Initialising client %d -> DATA region: %p\n", i, config.)*/
        client_queues[i] = i2c_queue_init(config.clients[i].conn.req_queue.vaddr,
                                          config.clients[i].conn.resp_queue.vaddr);
    }
}

void notified(microkit_channel ch)
{
    if (ch == config.driver.id) {
        LOG_VIRT("notified by driver\n");
        process_response();
    } else {
        LOG_VIRT("notified by client %u\n", ch - CLIENT_CH_OFFSET);
        process_request(ch - CLIENT_CH_OFFSET);
    }
}

seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t bus = microkit_mr_get(I2C_BUS_SLOT);
    uint32_t client_id = ch - CLIENT_CH_OFFSET;

    if (label != I2C_BUS_CLAIM && label != I2C_BUS_RELEASE) {
        LOG_VIRT_ERR("unknown label (0x%lx) given by client on channel 0x%x\n", label, ch);
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    if (bus > I2C_BUS_ADDRESS_MAX) {
        LOG_VIRT_ERR("invalid bus address (0x%lx) given by client on "
                     "channel 0x%x. Max bus address is 0x%x\n",
                     bus, ch, I2C_BUS_ADDRESS_MAX);
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    switch (label) {
    case I2C_BUS_CLAIM:
        // We have a valid bus address, we need to make sure no one else has claimed it.
        if (security_list[bus] != BUS_UNCLAIMED) {
            LOG_VIRT_ERR("bus address 0x%lx already claimed, cannot claim for channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(I2C_FAILURE, 0);
        }

        security_list[bus] = client_id;
        break;
    case I2C_BUS_RELEASE:
        if (security_list[bus] != client_id) {
            LOG_VIRT_ERR("bus address 0x%lx is not claimed by channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(I2C_FAILURE, 0);
        }

        security_list[bus] = BUS_UNCLAIMED;
        break;
    default:
        LOG_VIRT_ERR("reached unreachable case\n");
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    return microkit_msginfo_new(I2C_SUCCESS, 0);
}
