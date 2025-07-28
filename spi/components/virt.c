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

uint64_t cs_to_client_id[SPI_CS_MAX];

spi_cmd_t tx[NUM_QUEUE_ENTRIES];
uint32_t tx_len;
bool tx_cached;
spi_cs_t tx_cs;

__attribute__((__section__(".spi_virt_config"))) spi_virt_config_t config;

static inline void log_enqueue_resp_err(spi_err_t err, uint8_t err_cmd_idx, uint64_t client_id, 
        spi_cs_t cs) {
    LOG_VIRT("Failed to enqueue response (err=%s, err_cmd_idx=%u) into client %lu's CS %u queue\n", 
            err_to_str(err), err_cmd_idx, client_id, cs);
}

spi_err_t validate_cmd(spi_cmd_t *cmd, uint64_t data_region_size) {
    size_t read_offset = cmd->read_offset;
    size_t write_offset = cmd->read_offset; 
    size_t len = CMD_LEN(cmd->len);
    LOG_VIRT("CMD_LEN(len)=%lu\n", len);
    LOG_VIRT("data_size=%lu\n", data_region_size);

    bool reading = read_offset != -1;
    bool writing = write_offset != -1;
    size_t read_end = read_offset + len;
    size_t write_end = write_offset + len;

    bool read_unaligned = reading && read_offset & sizeof(uint32_t) - 1;
    bool write_unaligned = writing && write_offset & sizeof(uint32_t) - 1;
    if (read_unaligned || write_unaligned) {
        return SPI_ERR_UNALIGNED_OFFSET;
    }

    bool read_oob = reading && read_end >= data_region_size; 
    bool write_oob = writing && write_end >= data_region_size;
    if (read_oob || write_oob) {
        return SPI_ERR_OOB;
    }

    bool partial_overlap = reading && writing && 
        ((write_offset < read_offset  && read_offset  < write_end) || 
         (read_offset  < write_offset && write_offset < read_end ));
    if (partial_overlap) {
        return SPI_ERR_PARTIAL_OVERLAP;
    }

    return SPI_ERR_OK;
}

spi_resp_t find_next_tx(spi_cmd_queue_t *cmd_queue, uint64_t data_region_size) {
    spi_resp_t resp = (spi_resp_t) {SPI_ERR_OK, -1};

    uint32_t queue_len = spi_queue_length(cmd_queue->ctrl);
    for (tx_len = 0; tx_len < queue_len; tx_len++) {
        spi_cmd_t *cmd = &tx[tx_len];
        // TODO: remove assert since clients can cause this to fail in a multicore scenario
        assert(!spi_dequeue_cmd(
                cmd_queue, 
                &cmd->read_offset,
                &cmd->write_offset,
                &cmd->len,
                &cmd->cs_active_after_cmd
        ));

        LOG_VIRT("cmd %d: read_offset=%lu, write_offset=%lu, len=%u, csaac=%b\n",
            tx_len, cmd->read_offset, cmd->write_offset, cmd->len, cmd->cs_active_after_cmd);

        // Only validate the command if no other errors were encountered
        if (resp.err == SPI_ERR_OK) {
            resp = (spi_resp_t) {validate_cmd(cmd, data_region_size), tx_len};
        }

        // Only return early if the TX has terminated
        if (!cmd->cs_active_after_cmd) {
            tx_len++;
            return resp;
        }
    }

    // Should only be reachable if TX has not been terminated, or queue is empty
    return (spi_resp_t) {SPI_ERR_UNTERM_TX, -1};
}

void process_request(uint32_t client_id)
{
    spi_cmd_queue_t *driver_cmd_queue = config.driver.cmd_queue.vaddr;
    spi_cs_queue_t *cmd_cs_queue = config.driver.cmd_cs_queue.vaddr;
    // TODO: is this even logical?
    if (tx_cached) {
        // The driver's request queue should be empty
        assert(!spi_mass_enqueue_cmd(driver_cmd_queue, tx, tx_len));
        assert(!spi_enqueue_cs(cmd_cs_queue, tx_cs));
    }
    tx_cached = false;

    spi_cmd_queue_t *cmd_queue = config.clients[client_id].conn.cmd_queue.vaddr;
    spi_resp_queue_t *resp_queue = config.clients[client_id].conn.resp_queue.vaddr;
    spi_cs_t cs = config.clients[client_id].cs;
    uint64_t data_region_size = config.clients[client_id].data_size;

    do {
        spi_resp_t resp = find_next_tx(cmd_queue, data_region_size);
        LOG_VIRT("resp.err=%s\n", err_to_str(resp.err));
        if (resp.err == SPI_ERR_OK) {
            if (spi_mass_enqueue_cmd(driver_cmd_queue, tx, tx_len)) {
                tx_cached = true;
                tx_cs = cs;
            }
            else {
                assert(!spi_enqueue_cs(cmd_cs_queue, cs));
                LOG_VIRT("%p, cs - head: %u, tail=%u\n", cmd_cs_queue, cmd_cs_queue->ctrl.head, cmd_cs_queue->ctrl.tail);
                microkit_deferred_notify(config.driver.id);
            }
            return;
        }

        if (spi_enqueue_resp(resp_queue, resp.err, resp.err_cmd_idx)) {
            log_enqueue_resp_err(resp.err, resp.err_cmd_idx, client_id, cs);
        }
        if (resp.err == SPI_ERR_UNTERM_TX) {
            microkit_deferred_notify(config.clients[client_id].conn.id);
            return;
        }
    } while (spi_queue_length(cmd_queue->ctrl) > 0);

    // All erroneous and terminated transactions, notify the client
    microkit_deferred_notify(config.clients[client_id].conn.id);
    return;
}

uint8_t i = 0;
#define debug() LOG_VIRT("debug: %d\n", i++);

void process_response()
{
    spi_resp_queue_t *driver_resp_queue = config.driver.resp_queue.vaddr;
    spi_cs_queue_t *driver_cs_resp_queue = config.driver.resp_cs_queue.vaddr;
    while (!spi_queue_empty(driver_resp_queue->ctrl)) {
        spi_cs_t cs;
        uint16_t err_cmd_idx;
        spi_err_t err;

        LOG_VIRT("cs - head: %u, tail=%u\n", driver_cs_resp_queue->ctrl.head, driver_cs_resp_queue->ctrl.tail);

        assert(!spi_dequeue_cs(driver_cs_resp_queue, &cs));
        assert(!spi_dequeue_resp(driver_resp_queue, &err, &err_cmd_idx));        

        LOG_VIRT("cs=%d\n", cs);

        uint64_t client_id = cs_to_client_id[cs];
        spi_resp_queue_t *resp_queue = config.clients[client_id].conn.resp_queue.vaddr;
        LOG_VIRT("resp_queue=%p, client_id=%lu\n", resp_queue, client_id);
        if (spi_enqueue_resp(resp_queue, err, err_cmd_idx)) {
            log_enqueue_resp_err(err, err_cmd_idx, client_id, cs);
        }
        else {
            microkit_notify(CLIENT_CH_OFFSET + client_id);
        }
    }
}

void init(void)
{
    assert(spi_config_check_magic(&config));
    assert(config.driver.id == 0);
    assert(config.num_clients > 0);
    tx_cached = false;
    
    //TODO probe HW to check if all CS lines are valid

    // Reverse lookup table from CS to client IDs
    for (uint8_t i = 0; i < SPI_CS_MAX; i++) {
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

