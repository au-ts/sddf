/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/blk/queue.h>
#include <sddf/hotplug/hotplug.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

#include "serial_config.h"
#include "blk_config.h"

#define SERIAL_TX_CH    1
#define SERIAL_RX_CH    2
#define BLK_VIRT_CH     3

#define HOTPLUG_STATE_CLI0 4

#define PLUG_PRINT(...) do{ sddf_printf("PLUG: "); sddf_printf(__VA_ARGS__); }while(0)

serial_queue_t *rx_queue;
serial_queue_t *tx_queue;
char *rx_data;
char *tx_data;
serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

blk_queue_handle_t blk_queue;
blk_storage_info_t *blk_config;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
uint8_t *blk_data;

hotplug_shared_device_t *block_device;

void notified_serial()
{
    bool reprocess = true;
    char c;
    while (reprocess) {
        while (!serial_dequeue(&rx_queue_handle, &rx_queue_handle.queue->head, &c)) {
            if (c == '[') {
                PLUG_PRINT("Request for unplug\n");
                if (__atomic_load_n(&block_device->state, __ATOMIC_ACQUIRE) == SDDF_HOTPLUG_STATE_INSERTED) {
                    PLUG_PRINT("-> notifying clients\n");
                    sddf_hotplug_notify(HOTPLUG_STATE_CLI0, block_device, SDDF_HOTPLUG_STATE_EJECTING);

                    /* continued via the signal handler */
                } else {
                    PLUG_PRINT("-> already unplugging/ed\n");
                }
            } else if (c == '/') {

                /* only if the clients never set OK_TO_EJECT */
                if (__atomic_load_n(&block_device->state, __ATOMIC_ACQUIRE) == SDDF_HOTPLUG_STATE_EJECTING) {
                    PLUG_PRINT("Forcing an unmount\n");
                    /* force unmount ;p */
                    assert(!blk_enqueue_req(&blk_queue, BLK_REQ_UNMOUNT, 0, 0, 0, 1));
                    microkit_notify(BLK_VIRT_CH);
                }

            } else if (c == ']') {
                PLUG_PRINT("Request for plug\n");
                if (__atomic_load_n(&block_device->state, __ATOMIC_ACQUIRE) == SDDF_HOTPLUG_STATE_EJECTED) {
                    PLUG_PRINT("-> initialising driver, then notifying clients\n");

                    assert(!blk_enqueue_req(&blk_queue, BLK_REQ_MOUNT, 0, 0, 0, 0));
                    microkit_notify(BLK_VIRT_CH);

                    /* continued in the signal handler */
                } else {
                    PLUG_PRINT("-> either plugged or unplugging already: %u\n", block_device->state);
                }
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

void notified_hotplug(void)
{
    // TODO: multiple clients
    if (__atomic_load_n(&block_device->state, __ATOMIC_ACQUIRE) == SDDF_HOTPLUG_STATE_OK_TO_EJECT) {
        PLUG_PRINT("Hotplug notified: ok to eject\n");

        assert(!blk_enqueue_req(&blk_queue, BLK_REQ_UNMOUNT, 0, 0, 0, 1));
        microkit_notify(BLK_VIRT_CH);

        /* continued in signal handler */
    }
}

void notified_blk(void)
{
    blk_resp_status_t status;
    uint16_t success_count;
    uint32_t id;
    assert(!blk_dequeue_resp(&blk_queue, &status, &success_count, &id));

    /* kinda hacky, id: 0 => mount, 1 => unmount*/
    if (id == 0) {
        if (status != BLK_RESP_OK) {
            PLUG_PRINT("failed mount...!\n");
            return;
        }

        PLUG_PRINT("mounted\n");
        sddf_hotplug_notify(HOTPLUG_STATE_CLI0, block_device, SDDF_HOTPLUG_STATE_INSERTED);
    } else if (id == 1) {
        if (status != BLK_RESP_OK) {
            PLUG_PRINT("failed unmount...!\n");
            return;
        }

        PLUG_PRINT("ejeceted!\n");
        sddf_hotplug_notify(HOTPLUG_STATE_CLI0, block_device, SDDF_HOTPLUG_STATE_EJECTED);
    }
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case SERIAL_RX_CH:
        notified_serial();
        break;

    case SERIAL_TX_CH:
        PLUG_PRINT("notif on TX_CH?\n");
        break;

    case BLK_VIRT_CH:
        notified_blk();
        break;

    case HOTPLUG_STATE_CLI0:
        notified_hotplug();
        break;

    default:
        assert(!"unknown channel");
    }
}

void init(void)
{
    serial_cli_queue_init_sys("plug_controller", &rx_queue_handle, rx_queue, rx_data, &tx_queue_handle, tx_queue, tx_data);
    serial_putchar_init(SERIAL_TX_CH, &tx_queue_handle);

    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_SIZE_CLI1);
    /* Busy wait until blk device is ready */
    while (!__atomic_load_n(&blk_config->ready, __ATOMIC_ACQUIRE));

    sddf_printf("Hello from plug controller\n");
}
