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

#define CLIENT_CH_OFFSET (1)

uint64_t cs_to_client_id[SPI_MAX_CS_LINES];

spi_handle_t driver_handle;
spi_handle_t client_handles[SDDF_SPI_MAX_CLIENTS];

//TODO
spi_cmd_t tx[1 << 12];
uint32_t tx_len;
bool tx_cached;
spi_cs_t tx_cs;

__attribute__((__section__(".spi_virt_config"))) spi_virt_config_t config;

static inline void log_enqueue_resp_failure(spi_status_t status, uint8_t err_cmd_idx, uint64_t client_id, spi_cs_t cs)
{
    LOG_VIRT("Failed to enqueue response (status=%s, err_cmd_idx=%u) into client %lu's CS %u queue\n",
             spi_status_str(status), err_cmd_idx, client_id, cs);
}

spi_status_t validate_cmd(spi_cmd_t *cmd, uint64_t data_region_size)
{
    size_t read_offset = cmd->read_offset;
    size_t write_offset = cmd->read_offset;
    uint32_t len = CMD_LEN(cmd->len);
    LOG_VIRT("CMD_LEN(len)=%u\n", len);
    LOG_VIRT("data_size=%lu\n", data_region_size);

    bool reading = read_offset != -1;
    bool writing = write_offset != -1;
    size_t read_end = read_offset + len;
    size_t write_end = write_offset + len;

    bool read_unaligned = reading && read_offset & sizeof(uint32_t) - 1;
    bool write_unaligned = writing && write_offset & sizeof(uint32_t) - 1;
    if (read_unaligned || write_unaligned) {
        return SPI_STATUS_ERR_CMD_UNALIGNED_OFFSET;
    }

    bool read_oob = reading && read_end >= data_region_size;
    bool write_oob = writing && write_end >= data_region_size;
    if (read_oob || write_oob) {
        return SPI_STATUS_ERR_CMD_OOB;
    }

    bool partial_overlap = reading && writing
                        && ((write_offset < read_offset && read_offset < write_end)
                            || (read_offset < write_offset && write_offset < read_end));
    if (partial_overlap) {
        return SPI_STATUS_ERR_CMD_PARTIAL_OVERLAP;
    }

    return SPI_STATUS_OK;
}

spi_resp_t find_next_tx(spi_handle_t *handle, uint64_t data_region_size)
{
    spi_resp_t resp = (spi_resp_t) { SPI_STATUS_OK, -1 };

    uint32_t queue_len = spi_cmd_queue_len(handle);
    for (tx_len = 0; tx_len < queue_len; tx_len++) {
        spi_cmd_t *cmd = &tx[tx_len];
        // TODO: remove assert since clients can cause this to fail in a multicore scenario
        assert(spi_dequeue_cmd(handle, &cmd->read_offset, &cmd->write_offset, &cmd->len, &cmd->cs_active_after_cmd));

        LOG_VIRT("cmd %d: read_offset=%lu, write_offset=%lu, len=%u, csaac=%b\n", tx_len, cmd->read_offset,
                 cmd->write_offset, cmd->len, cmd->cs_active_after_cmd);

        // Only validate the command if no other errors were encountered
        if (resp.status == SPI_STATUS_OK) {
            resp = (spi_resp_t) { validate_cmd(cmd, data_region_size), tx_len };
        }

        // Only return early if the TX has terminated
        if (!cmd->cs_active_after_cmd) {
            tx_len++;
            return resp;
        }
    }

    // Should only be reachable if TX has not been terminated, or queue is empty
    return (spi_resp_t) { SPI_STATUS_ERR_PARTIAL_TXN, -1 };
}

void process_request(uint32_t client_id)
{
    // TODO: is this even logical?
    if (tx_cached) {
        // The driver's request queue should be empty
        assert(spi_mass_enqueue_cmd(&driver_handle, tx, tx_len));
        assert(spi_enqueue_cmd_cs(&driver_handle, tx_cs));
    }
    tx_cached = false;

    spi_handle_t *client_handle = &client_handles[client_id];
    spi_cs_t cs = config.clients[client_id].cs;
    uint64_t data_region_size = config.clients[client_id].data_size;

    do {
        spi_resp_t resp = find_next_tx(client_handle, data_region_size);
        LOG_VIRT("resp.status=%s\n", spi_status_str(resp.status));
        if (resp.status == SPI_STATUS_OK) {
            if (!spi_mass_enqueue_cmd(&driver_handle, tx, tx_len)) {
                tx_cached = true;
                tx_cs = cs;
            } else {
                assert(spi_enqueue_cmd_cs(&driver_handle, cs));
                microkit_deferred_notify(config.driver.id);
            }
            return;
        }

        if (spi_enqueue_resp(&driver_handle, resp.status, resp.err_cmd_idx)) {
            log_enqueue_resp_failure(resp.status, resp.err_cmd_idx, client_id, cs);
        }
        if (resp.status == SPI_STATUS_ERR_PARTIAL_TXN) {
            microkit_deferred_notify(config.clients[client_id].conn.id);
            return;
        }
    } while (spi_cmd_queue_len(client_handle) > 0);

    // All erroneous and terminated transactions, notify the client
    microkit_deferred_notify(config.clients[client_id].conn.id);
    return;
}

void process_response()
{
    while (!spi_resp_queue_empty(&driver_handle)) {
        spi_cs_t cs;
        uint16_t err_cmd_idx;
        spi_status_t err;

        LOG_VIRT("handle.queue_capacity_bits=%d\n", driver_handle.queue_capacity_bits);
        LOG_VIRT("resp_cs_queue.len=%d\n", spi_resp_cs_queue_len(&driver_handle));
        LOG_VIRT("resp_queue.len=%d\n", spi_resp_queue_len(&driver_handle));
        LOG_VIRT("&ptr=%p\n", driver_handle.spi_resp_cs_queue);

        assert(spi_dequeue_resp_cs(&driver_handle, &cs));
        assert(spi_dequeue_resp(&driver_handle, &err, &err_cmd_idx));

        LOG_VIRT("cs=%d\n", cs);

        uint64_t client_id = cs_to_client_id[cs];
        LOG_VIRT("client_id=%lu\n", client_id);
        if (!spi_enqueue_resp(&client_handles[client_id], err, err_cmd_idx)) {
            log_enqueue_resp_failure(err, err_cmd_idx, client_id, cs);
        } else {
            microkit_notify(CLIENT_CH_OFFSET + client_id);
        }
    }
}

void init(void)
{
    assert(spi_config_check_magic(&config));
    assert(config.driver.id == 0);
    assert(config.num_clients > 0);

    assert(spi_handle_init(&driver_handle, config.driver.cmd_queue.vaddr, config.driver.resp_queue.vaddr,
                           config.driver.cmd_cs_queue.vaddr, config.driver.resp_cs_queue.vaddr,
                           config.driver.queue_capacity_bits));

    for (uint8_t i = 0; i < config.num_clients; i++) {
        assert(spi_handle_init(&client_handles[i], config.clients[i].conn.cmd_queue.vaddr,
                               config.clients[i].conn.resp_queue.vaddr, NULL, NULL,
                               config.clients[i].conn.queue_capacity_bits));
    }

    tx_cached = false;

    //TODO probe HW to check if all CS lines are valid

    // Reverse lookup table from CS to client IDs
    for (uint8_t i = 0; i < SPI_MAX_CS_LINES; i++) {
        cs_to_client_id[i] = -1;
    }
    for (uint8_t i = 0; i < config.num_clients; i++) {
        spi_cs_t cs = config.clients[i].cs;
        uint64_t client_id = config.clients[i].conn.id - CLIENT_CH_OFFSET;
        LOG_VIRT("%d: cs=%d, client_id=%ld\n", i, cs, client_id);
        cs_to_client_id[cs] = client_id;
    }
}

void notified(microkit_channel ch)
{
    microkit_channel client_id = ch - CLIENT_CH_OFFSET;
    if (ch == config.driver.id) {
        LOG_VIRT("notified by driver\n");
        process_response();
    } else if (client_id < config.num_clients) {
        LOG_VIRT("notified by client %u\n", client_id);
        process_request(client_id);
    } else {
        LOG_VIRT_ERR("spuriously notified on channel %d\n", ch);
    }
}
