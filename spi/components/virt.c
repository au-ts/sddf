/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>
#include <sddf/spi/queue.h>
#include <sddf/spi/config.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define DEBUG_VIRT

#ifdef DEBUG_VIRT
#define LOG_VIRT(...) do{ sddf_dprintf("SPI VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRT(...) do{}while(0)
#endif

#define LOG_VIRT_ERR(...) do{ sddf_printf("SPI VIRT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define BUS_UNCLAIMED (-1)

#define CLIENT_CH_OFFSET 1

__attribute__((__section__(".spi_virt_config"))) spi_virt_config_t config;

spi_queue_handle_t client_queues[SDDF_SPI_MAX_CLIENTS];
spi_queue_handle_t driver_queue;

// Security list: owner of each spi address on the bus
int security_list[SPI_CS_LINES_MAX];

void process_request(uint32_t client_id)
{
    bool enqueued = false;
    assert(client_id < config.num_clients);

    /* Do not process the request if we cannot pass it to the driver */
    while (!spi_queue_empty(client_queues[client_id].request->ctrl) && !spi_queue_full(driver_queue.request->ctrl)) {
        spi_cs_line_t cs_line;
        uintptr_t control_start_vaddr;
        uintptr_t slice_base_vaddr;
        uint16_t len;

        // Take request from client
        int err = spi_dequeue_request(client_queues[client_id], &cs_line, &control_start_vaddr, &slice_base_vaddr,
                                      &len);
        if (err) {
            LOG_VIRT_ERR("could not dequeue from request queue\n");
            return;
        }

        // Check that client can actually access bus
        if (cs_line > SPI_CS_LINES_MAX || security_list[cs_line] != client_id) {
            LOG_VIRT_ERR("invalid bus address (0x%x) requested by client 0x%x\n", cs_line, client_id);
            continue;
        }
        LOG_VIRT("Request: bus address = %u : control = %p : len = %u\n", cs_line, (void *)control_start_vaddr, len);
        LOG_VIRT("Data origin for this client: %p\n", (void *)config.clients[client_id].client_control_vaddr);

        size_t offset = (size_t)control_start_vaddr - (size_t)config.clients[client_id].client_control_vaddr;
        LOG_VIRT("request offset: %zu\n", offset);
        if (offset > config.clients[client_id].control_size
            || control_start_vaddr > config.clients[client_id].driver_control_vaddr) {
            LOG_VIRT_ERR("invalid control vaddr (0x%lx) given by client %u.", control_start_vaddr, client_id);
            continue;
        }

        // Now we need to convert the offset into an offset the driver can use in its address space.
        uintptr_t driver_control_vaddr = (uintptr_t)(config.clients[client_id].driver_control_vaddr + offset);

        // We replace the slice base of the client with the driver's base. The client doesn't need
        // to supply one at all!
        LOG_VIRT("Enqueueing request to driver...\n");
        err = spi_enqueue_request(driver_queue, cs_line, driver_control_vaddr,
                                  config.clients[client_id].driver_slice_vaddr, len);

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
    while (!spi_queue_empty(driver_queue.response->ctrl)) {
        LOG_VIRT("Handling response...\n");
        spi_cs_line_t cs_line = 0;
        spi_err_t error = 0;
        size_t err_cmd = 0;

        /* We trust the driver to give us a sane bus address */
        int err = spi_dequeue_response(driver_queue, &cs_line, &error, &err_cmd);
        /* If this assert fails we have a race as the virtualiser should be the only one dequeuing
         * from the driver's response queue */
        assert(!err);

        size_t client_id = security_list[cs_line];
        if (client_id == BUS_UNCLAIMED) {
            LOG_VIRT_ERR("Driver response belongs to no authenticated client!\n");
            /* The client has released the bus before receiving all their responses, so we simply
             * drop the response. */
            continue;
        }

        /* There is no point checking if the enqueue succeeds or not. */
        spi_enqueue_response(client_queues[client_id], cs_line, error, err_cmd);

        LOG_VIRT("Notifying client.\n");
        microkit_notify(CLIENT_CH_OFFSET + client_id);
    }
}

void init(void)
{
    assert(spi_config_check_magic(&config));
    assert(config.driver.id == 0);  // @leslr: is this needed? sdfgen should remove any need
    LOG_VIRT("initialising\n");
    for (int i = 0; i < SPI_CS_LINES_MAX; i++) {
        security_list[i] = BUS_UNCLAIMED;
    }
    driver_queue = spi_queue_init(config.driver.req_queue.vaddr, config.driver.resp_queue.vaddr);

    for (int i = 0; i < config.num_clients; i++) {
        LOG_VIRT("Initialising client %d -> CONTROL region: %p\n", i, (void *) config.clients[i].client_control_vaddr);
        client_queues[i] = spi_queue_init(config.clients[i].conn.req_queue.vaddr,
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

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t bus = microkit_mr_get(SPI_BUS_SLOT);
    uint32_t client_id = ch - CLIENT_CH_OFFSET;

    if (label != SPI_BUS_CLAIM && label != SPI_BUS_RELEASE) {
        LOG_VIRT_ERR("unknown label (0x%lx) given by client on channel 0x%x\n", label, ch);
        return microkit_msginfo_new(SPI_FAILURE, 0);
    }

    if (bus > SPI_CS_LINES_MAX) {
        LOG_VIRT_ERR("invalid bus address (0x%lx) given by client on channel 0x%x. Max bus address is 0x%x\n",
                     bus, ch, SPI_CS_LINES_MAX);
        return microkit_msginfo_new(SPI_FAILURE, 0);
    }

    uint64_t argc, cpha, cpol;

    switch (label) {
    case SPI_BUS_CLAIM:
        argc = microkit_msginfo_get_count(msginfo);
        if (argc != SPI_BUS_CLAIM_ARGC) {
            LOG_VIRT_ERR("expected %d arguments, channel 0x%x sent %zu instead\n", 
                SPI_BUS_CLAIM_ARGC, ch, argc);
        }

        // We have a valid bus address, we need to make sure no one else has claimed it.
        if (security_list[bus] != BUS_UNCLAIMED) {
            LOG_VIRT_ERR("bus address 0x%lx already claimed, cannot claim for channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(SPI_FAILURE, 0);
        }

        // Validate clock phase
        cpha = microkit_mr_get(SPI_CPHA_SLOT);
        if (cpha != SPI_CPHA_FIRST && cpha != SPI_CPHA_SECOND) {
            LOG_VIRT_ERR("channel 0x%x provided an invalid clock phase\n", ch);
            return microkit_msginfo_new(SPI_FAILURE, 0);
        }

        // Validate clock polarity
        cpol = microkit_mr_get(SPI_CPOL_SLOT);
        if (cpol != SPI_CPOL_HIGH && cpol != SPI_CPOL_LOW) {
            LOG_VIRT_ERR("channel 0x%x provided an invalid clock polarity\n", ch);
            return microkit_msginfo_new(SPI_FAILURE, 0);
        }

        // Setup PPC
        microkit_msginfo msginfo = microkit_msginfo_new(SPI_BUS_CONFIG, 3);
        microkit_mr_set(SPI_BUS_SLOT, bus);
        microkit_mr_set(SPI_CPOL_SLOT, cpol);
        microkit_mr_set(SPI_CPOL_SLOT, cpha);
        msginfo = microkit_ppcall(config.driver.id, msginfo);

        if (microkit_msginfo_get_label(msginfo) == SPI_FAILURE) {
            LOG_VIRT_ERR("failure in configuring bus address 0x%zx for channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(SPI_FAILURE, 0);
        }

        security_list[bus] = client_id;
        break;
    case SPI_BUS_RELEASE:
        if (security_list[bus] != client_id) {
            LOG_VIRT_ERR("bus address 0x%lx is not claimed by channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(SPI_FAILURE, 0);
        }

        security_list[bus] = BUS_UNCLAIMED;
        break;
    default:
        LOG_VIRT_ERR("reached unreachable case\n");
        return microkit_msginfo_new(SPI_FAILURE, 0);
    }

    return microkit_msginfo_new(SPI_SUCCESS, 0);
}
