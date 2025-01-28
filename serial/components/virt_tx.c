/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/printf.h>

#define NAME_MAX 128
#define BEGIN_STR_MAX 128

__attribute__((__section__(".serial_virt_tx_config"))) serial_virt_tx_config_t config;

/* When we have more clients than colours, we re-use the colours. */
const char *colours[] = {
    /* foreground red */
    "\x1b[31m",
    /* foreground green */
    "\x1b[32m",
    /* foreground yellow */
    "\x1b[33m",
    /* foreground blue */
    "\x1b[34m",
    /* foreground magenta */
    "\x1b[35m",
    /* foreground cyan */
    "\x1b[36m"
};

#define COLOUR_BEGIN_LEN 5
#define COLOUR_END "\x1b[0m"
#define COLOUR_END_LEN 4

char client_names[NAME_MAX][SDDF_SERIAL_MAX_CLIENTS];

serial_queue_handle_t tx_queue_handle_drv;
serial_queue_handle_t tx_queue_handle_cli[SDDF_SERIAL_MAX_CLIENTS];

#define TX_PENDING_MAX (SDDF_SERIAL_MAX_CLIENTS + 1)
typedef struct tx_pending {
    uint32_t queue[TX_PENDING_MAX];
    bool clients_pending[SDDF_SERIAL_MAX_CLIENTS];
    uint32_t head;
    uint32_t tail;
} tx_pending_t;

tx_pending_t tx_pending;

static uint32_t tx_pending_length(void)
{
    return (TX_PENDING_MAX + tx_pending.tail - tx_pending.head) % TX_PENDING_MAX;
}

static void tx_pending_push(uint32_t client)
{
    /* Ensure client is not already pending */
    if (tx_pending.clients_pending[client]) {
        return;
    }

    /* Ensure the pending queue is not already full */
    assert(tx_pending_length() < config.num_clients);

    tx_pending.queue[tx_pending.tail] = client;
    tx_pending.clients_pending[client] = true;
    tx_pending.tail = (tx_pending.tail + 1) % TX_PENDING_MAX;
}

static void tx_pending_pop(uint32_t *client)
{
    /* This should only be called when length > 0 */
    assert(tx_pending_length());

    *client = tx_pending.queue[tx_pending.head];
    tx_pending.clients_pending[*client] = false;
    tx_pending.head = (tx_pending.head + 1) % TX_PENDING_MAX;
}

bool process_tx_queue(uint32_t client)
{
    serial_queue_handle_t *handle = &tx_queue_handle_cli[client];

    if (serial_queue_empty(handle, handle->queue->head)) {
        return false;
    }

    uint32_t length = serial_queue_length(handle);
    if (config.enable_colour) {
        const char *client_colour = colours[client % ARRAY_SIZE(colours)];
        assert(COLOUR_BEGIN_LEN == sddf_strlen(client_colour));
        length += COLOUR_BEGIN_LEN + COLOUR_END_LEN;
    }

    /* Not enough space to transmit string to virtualiser. Continue later */
    if (length > serial_queue_free(&tx_queue_handle_drv)) {
        tx_pending_push(client);

        /* Request signal from the driver when data has been consumed */
        serial_request_consumer_signal(&tx_queue_handle_drv);
        return false;
    }

    if (config.enable_colour) {
        const char *client_colour = colours[client % ARRAY_SIZE(colours)];
        serial_transfer_all_colour(&tx_queue_handle_drv, handle, client_colour, COLOUR_BEGIN_LEN, COLOUR_END,
                                   COLOUR_END_LEN);
    } else {
        serial_transfer_all(&tx_queue_handle_drv, handle);
    }

    return true;
}

void tx_return(void)
{
    uint32_t num_pending_tx = tx_pending_length();
    if (!num_pending_tx) {
        return;
    }

    uint32_t client;
    // TODO: `= {false};` gets optimised into memset
    bool notify_client[SDDF_SERIAL_MAX_CLIENTS];
    for (int i = 0; i < SDDF_SERIAL_MAX_CLIENTS; i++) {
        notify_client[i] = false;
    }
    bool transferred = false;
    for (uint32_t req = 0; req < num_pending_tx; req++) {
        tx_pending_pop(&client);
        notify_client[client] = process_tx_queue(client);
        transferred |= notify_client[client];
    }

    if (transferred) {
        sddf_notify(config.driver.id);
    }

    for (uint32_t client = 0; client < config.num_clients; client++) {
        if (notify_client[client] && serial_require_consumer_signal(&tx_queue_handle_cli[client])) {
            serial_cancel_consumer_signal(&tx_queue_handle_cli[client]);
            sddf_notify(config.clients[client].conn.id);
        }
    }
}

void tx_provide(sddf_channel ch)
{
    uint32_t active_client = SDDF_SERIAL_MAX_CLIENTS;
    for (int i = 0; i < config.num_clients; i++) {
        if (ch == config.clients[i].conn.id) {
            active_client = i;
            break;
        }
    }

    if (active_client == SDDF_SERIAL_MAX_CLIENTS) {
        sddf_dprintf("VIRT_TX|LOG: Received notification from unknown channel %u\n", ch);
        return;
    }

    bool transferred = process_tx_queue(active_client);
    if (transferred) {
        sddf_notify(config.driver.id);
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle_cli[active_client])) {
        serial_cancel_consumer_signal(&tx_queue_handle_cli[active_client]);
        sddf_notify(ch);
    }
}

void init(void)
{
    assert(serial_config_check_magic(&config));

    serial_queue_init(&tx_queue_handle_drv, config.driver.queue.vaddr, config.driver.data.size,
                      config.driver.data.vaddr);
    for (uint64_t i = 0; i < config.num_clients; i++) {
        serial_virt_tx_client_config_t *client = &config.clients[i];
        serial_queue_init(&tx_queue_handle_cli[i], client->conn.queue.vaddr, client->conn.data.size,
                          client->conn.data.vaddr);
    }

    if (config.enable_rx) {
        /* Print a deterministic string to allow console input to begin */
        sddf_memcpy(tx_queue_handle_drv.data_region, config.begin_str, config.begin_str_len + 1);
        serial_update_shared_tail(&tx_queue_handle_drv, config.begin_str_len + 1);
        sddf_notify(config.driver.id);
    }

    if (config.enable_colour) {
        for (uint64_t i = 0; i < config.num_clients; i++) {
            for (int j = 0; j < NAME_MAX; j++) {
                sddf_memcpy(client_names[i], config.clients[i].name, sizeof client_names[i]);
            }
            sddf_dprintf("%s'%s' is client %lu%s\n", colours[i % ARRAY_SIZE(colours)], client_names[i], i, COLOUR_END);
        }
    }
}

void notified(sddf_channel ch)
{
    if (ch == config.driver.id) {
        tx_return();
    } else {
        tx_provide(ch);
    }
}
