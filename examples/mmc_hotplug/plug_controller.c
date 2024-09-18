/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/hotplug/clients.h>
#include <sddf/hotplug/control.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

#include "serial_config.h"
#include "blk_config.h"

#define SERIAL_TX_CH 1
#define SERIAL_RX_CH 2
#define BLK_QUEUE_CH 3
#define BLK_STATE_CH 4
#define CLIS_BASE_CH 5

#define PLUG_PRINT(...) do{ sddf_printf("PLUG: "); sddf_printf(__VA_ARGS__); }while(0)

serial_queue_t *rx_queue;
serial_queue_t *tx_queue;
char *rx_data;
char *tx_data;
serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

blk_storage_info_t *blk_storage_info;

// TODO: All of these are unnecessary.
blk_queue_handle_t blk_queue;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
uint8_t *blk_data;

// Patched by microkit.
hotplug_info_t *hotplug_client0_info;
static hotplug_info_t **clients_info[] = { &hotplug_client0_info };
#define NUM_CLIENTS (ARRAY_SIZE(clients_info))
static int clients_safe_to_eject[NUM_CLIENTS] = { 0 };
static int num_clients_safe_to_eject = 0;

void hotplug_notify_clients(bool pending_eject)
{
    num_clients_safe_to_eject = 0;
    for (int i = 0; i < NUM_CLIENTS; i++) {
        clients_safe_to_eject[i] = false;
        hotplug_set_pending_eject(*clients_info[i], CLIS_BASE_CH + i, pending_eject);
    }
}

void notified_serial()
{
    bool reprocess = true;

    microkit_msginfo msginfo;
    char c;
    while (reprocess) {
        while (!serial_dequeue(&rx_queue_handle, &rx_queue_handle.queue->head, &c)) {
            if (c == '[') {
                PLUG_PRINT("Notifying clients of pending EJECT...\n");
                hotplug_notify_clients(/* pending eject */ true);

            } else if (c == '/') {

                PLUG_PRINT("Forcing ejection...\n");
                msginfo = microkit_ppcall(BLK_STATE_CH, microkit_msginfo_new(SDDF_HOTPLUG_REQ_EJECT, 0));
                PLUG_PRINT("-> response: %lu\n", microkit_msginfo_get_label(msginfo));

            } else if (c == ']') {
                PLUG_PRINT("Requesting card insert (n.b. driver will usually autodetect)\n");
                msginfo = microkit_ppcall(BLK_STATE_CH, microkit_msginfo_new(SDDF_HOTPLUG_REQ_INSERT, 0));
                PLUG_PRINT("-> response: %lu\n", microkit_msginfo_get_label(msginfo));
            }
        }

        // I have no idea what this is.
        serial_request_producer_signal(&rx_queue_handle);
        reprocess = false;

        if (!serial_queue_empty(&rx_queue_handle, rx_queue_handle.queue->head)) {
            serial_cancel_producer_signal(&rx_queue_handle);
            reprocess = true;
        }
    }
}

void notified_blk_state(void)
{
    if (blk_storage_is_ready(blk_storage_info)) {
        PLUG_PRINT("Storage is now ready\n");
    } else {
        PLUG_PRINT("Storage is now not ready\n");
    }

    /* reset the pending eject states */
    hotplug_notify_clients(false);
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case SERIAL_RX_CH:
        notified_serial();
        break;

    case SERIAL_TX_CH:
        /* huh ? */
        break;

    case BLK_QUEUE_CH:
        assert(!"unexpected");
        break;

    case BLK_STATE_CH:
        notified_blk_state();
        break;

    default:
        assert(!"unknown channel");
    }
}

microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    /* we only set up clients with ppcall ability, so channel is always OK. */
    int client_index = ch - CLIS_BASE_CH;
    PLUG_PRINT("Safe to eject from client number %d\n", client_index);
    clients_safe_to_eject[client_index] = true;
    num_clients_safe_to_eject++;

    if (num_clients_safe_to_eject == NUM_CLIENTS) {
        PLUG_PRINT("All clients responded... ejecting\n");
        microkit_msginfo msginfo = microkit_ppcall(BLK_STATE_CH, microkit_msginfo_new(SDDF_HOTPLUG_REQ_EJECT, 0));
        PLUG_PRINT("-> response: %lu\n", microkit_msginfo_get_label(msginfo));
    }

    /* return: void */
    return microkit_msginfo_new(0, 0);
}

void init(void)
{
    serial_cli_queue_init_sys("plug_controller", &rx_queue_handle, rx_queue, rx_data, &tx_queue_handle, tx_queue,
                              tx_data);
    serial_putchar_init(SERIAL_TX_CH, &tx_queue_handle);
    // This is unnecessary for this client...
    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_SIZE_CLI1);

    sddf_printf("Hello from plug controller\n");
}
