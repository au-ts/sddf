/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sddf/serial/queue.h>
#include <sddf/util/printf.h>
#include "virt_tx_config.h"

#define MAX_CLIENTS (MICROKIT_MAX_CHANNELS - 1)
#define DRIVER_CH 0
#define CLIENT_OFFSET 1
#define NAME_MAX 128
#define BEGIN_STR_MAX 128

typedef struct config_client {
    char name[NAME_MAX];
    void *tx_queue;
    void *tx_data;
    uint64_t tx_capacity;
} config_client_t;

typedef struct config {
    void *tx_queue_drv;
    void *tx_data_drv;
    uint64_t tx_capacity_drv;
    char begin_str[BEGIN_STR_MAX];
    uint64_t begin_str_len;
    bool enable_colour;
    bool enable_rx;
    uint64_t num_clients;
    config_client_t clients[MAX_CLIENTS];
} config_t;

config_t config;

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

char client_names[NAME_MAX][MAX_CLIENTS];

serial_queue_handle_t tx_queue_handle_drv;
serial_queue_handle_t tx_queue_handle_cli[MAX_CLIENTS];

#define TX_PENDING_MAX (MAX_CLIENTS + 1)
typedef struct tx_pending {
    uint32_t queue[TX_PENDING_MAX];
    bool clients_pending[MAX_CLIENTS];
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
        serial_request_producer_signal(handle);
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

        /* Cancel further signals from this client */
        serial_cancel_producer_signal(handle);
        return false;
    }

    if (config.enable_colour) {
        const char *client_colour = colours[client % ARRAY_SIZE(colours)];
        serial_transfer_all_with_colour(handle, &tx_queue_handle_drv, client_colour, COLOUR_BEGIN_LEN,
                                        COLOUR_END, COLOUR_END_LEN);
    } else {
        serial_transfer_all(handle, &tx_queue_handle_drv);
    }
    serial_request_producer_signal(handle);
    return true;
}

void tx_return(void)
{
    uint32_t num_pending_tx = tx_pending_length();
    if (!num_pending_tx) {
        return;
    }

    uint32_t client;
    bool notify_client[MAX_CLIENTS] = {false};
    bool transferred = false;
    for (uint32_t req = 0; req < num_pending_tx; req++) {
        tx_pending_pop(&client);
        bool reprocess = true;
        bool client_transferred = false;
        while (reprocess) {
            client_transferred |= process_tx_queue(client);
            reprocess = false;

            /* If more data is available, re-process unless it has been pushed to pending transmits */
            if (!serial_queue_empty(&tx_queue_handle_cli[client], tx_queue_handle_cli[client].queue->head)
                && !tx_pending.clients_pending[client]) {
                serial_cancel_producer_signal(&tx_queue_handle_cli[client]);
                reprocess = true;
            }
        }
        transferred |= client_transferred;
        notify_client[client] = client_transferred;
    }

    if (transferred && serial_require_producer_signal(&tx_queue_handle_drv)) {
        serial_cancel_producer_signal(&tx_queue_handle_drv);
        microkit_notify(DRIVER_CH);
    }

    for (uint32_t client = 0; client < config.num_clients; client++) {
        if (notify_client[client] && serial_require_consumer_signal(&tx_queue_handle_cli[client])) {
            serial_cancel_consumer_signal(&tx_queue_handle_cli[client]);
            microkit_notify(CLIENT_OFFSET + client);
        }
    }
}

void tx_provide(microkit_channel ch)
{
    if (ch > config.num_clients) {
        sddf_dprintf("VIRT_TX|LOG: Received notification from unknown channel %u\n", ch);
        return;
    }

    uint32_t active_client = ch - CLIENT_OFFSET;
    bool transferred = false;
    bool reprocess = true;
    while (reprocess) {
        transferred |= process_tx_queue(active_client);
        reprocess = false;

        /* If more data is available, re-process unless it has been pushed to pending transmits */
        if (!serial_queue_empty(&tx_queue_handle_cli[active_client], tx_queue_handle_cli[active_client].queue->head)
            && !tx_pending.clients_pending[active_client]) {
            serial_cancel_producer_signal(&tx_queue_handle_cli[active_client]);
            reprocess = true;
        }
    }

    if (transferred && serial_require_producer_signal(&tx_queue_handle_drv)) {
        serial_cancel_producer_signal(&tx_queue_handle_drv);
        microkit_notify(DRIVER_CH);
    }

    if (transferred && serial_require_consumer_signal(&tx_queue_handle_cli[active_client])) {
        serial_cancel_consumer_signal(&tx_queue_handle_cli[active_client]);
        microkit_notify(ch);
    }
}

void init(void)
{
    sddf_memcpy(&config, serial_virt_tx_data, serial_virt_tx_data_len);

    // config.tx_queue_drv = (void *)0x4000000;
    // config.tx_data_drv = (void *)0x4003000;
    // config.tx_capacity_drv = 0x2000;
    // sddf_memcpy(config.begin_str, "Begin input\n", 13);
    // config.begin_str_len = 13;
    // config.enable_colour = true;
    // config.enable_rx = true;
    // config.num_clients = 2;
    // sddf_memcpy(config.clients[0].name, "client0", 8);
    // config.clients[0].tx_queue = (void *)0x4001000;
    // config.clients[0].tx_data = (void *)0x4007000;
    // config.clients[0].tx_capacity = 0x2000;
    // sddf_memcpy(config.clients[1].name, "client1", 8);
    // config.clients[1].tx_queue = (void *)0x4002000;
    // config.clients[1].tx_data = (void *)0x4009000;
    // config.clients[1].tx_capacity = 0x2000;
    
    sddf_dprintf("DRIVER_CH = %d\n", DRIVER_CH);
    sddf_dprintf("config.tx_queue_drv = 0x%lx\n", config.tx_queue_drv);
    sddf_dprintf("config.tx_data_drv = 0x%lx\n", config.tx_data_drv);
    sddf_dprintf("config.tx_capacity_drv = 0x%x\n", config.tx_capacity_drv);
    sddf_dprintf("config.begin_str = %s", config.begin_str);
    sddf_dprintf("config.begin_str_len = %d\n", config.begin_str_len);
    sddf_dprintf("config.enable_colour = %d\n", config.enable_colour);
    sddf_dprintf("config.enable_rx = %d\n", config.enable_rx);
    sddf_dprintf("config.num_clients = %d\n", config.num_clients);
    for (int i = 0; i < config.num_clients; i++) {
        sddf_dprintf("config.clients[%d].name = %s\n", i, config.clients[i].name);
        sddf_dprintf("config.clients[%d].tx_queue = 0x%lx\n", i, config.clients[i].tx_queue);
        sddf_dprintf("config.clients[%d].tx_data = 0x%lx\n", i, config.clients[i].tx_data);
        sddf_dprintf("config.clients[%d].tx_capacity = 0x%x\n", i, config.clients[i].tx_capacity);
    }

    serial_queue_init(&tx_queue_handle_drv, config.tx_queue_drv, config.tx_capacity_drv, config.tx_data_drv);
    for (uint64_t i = 0; i < config.num_clients; i++) {
        config_client_t *client = &config.clients[i];
        serial_queue_init(&tx_queue_handle_cli[i], client->tx_queue, client->tx_capacity, client->tx_data);
    }

    if (config.enable_rx) {
        /* Print a deterministic string to allow console input to begin */
        sddf_memcpy(tx_queue_handle_drv.data_region, config.begin_str, config.begin_str_len + 1);
        serial_update_visible_tail(&tx_queue_handle_drv, config.begin_str_len + 1);
        microkit_notify(DRIVER_CH);
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

void notified(microkit_channel ch)
{
    switch (ch) {
    case DRIVER_CH:
        tx_return();
        break;
    default:
        tx_provide(ch);
        break;
    }
}
