/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/hotplug/clients.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

#include "blk_config.h"

#define CHANNEL_BLK_QUEUE 0
#define CHANNEL_BLK_STATE 1
#define CHANNEL_HOTPLUG   2

blk_queue_handle_t blk_queue;
blk_storage_info_t *blk_storage_info;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
uint8_t *blk_data;

hotplug_info_t *hotplug_info;

static uint32_t request_id = 0;
static uint32_t done_request_id;
static bool is_playing = false;
static bool pending_eject = false;

#define GAME_PRINT(...) do{ sddf_printf("GAME: "); sddf_printf(__VA_ARGS__); }while(0)

void play_our_game_stage(uint8_t stage)
{
    for (int i = 0; i < BLK_TRANSFER_SIZE; i++) {
        blk_data[stage * BLK_TRANSFER_SIZE + i] = stage;
    }
}

void play_our_game(void)
{
    is_playing = true;

    int err;
    for (int stage = 150; stage <= UINT8_MAX; stage++) {
        play_our_game_stage(stage);
        err = blk_enqueue_req(&blk_queue, BLK_REQ_WRITE, /* data offset */ stage * BLK_TRANSFER_SIZE,
                              /* block number */ 0x0, /* block count */ 1, request_id++);
        assert(!err);

        /* not strictly necessary, but let's do this anyway */
        err = blk_enqueue_req(&blk_queue, BLK_REQ_FLUSH, 0, 0, 0, request_id++);
        assert(!err);
    }

    microkit_notify(CHANNEL_BLK_QUEUE);

    done_request_id = request_id - 1;
    GAME_PRINT("Enqueued a playthrough\n");
}

void notified_blk_virt(void)
{
    if (!is_playing) {
        return;
    }

    bool did_finish = false;
    bool did_fail = false;
    while (!blk_queue_empty_resp(&blk_queue)) {
        blk_resp_status_t status;
        uint16_t success_count;
        uint32_t id;
        int err = blk_dequeue_resp(&blk_queue, &status, &success_count, &id);
        assert(!err);

        if (status != BLK_RESP_OK) {
            /* only print it out once */
            if (!did_fail) {
                GAME_PRINT("Received 1 or more non-successful queue response...\n");
                GAME_PRINT("-> 1st: status: %u, count: %u, id: %u\n", status, success_count, id);
                did_fail = true;
            }
            continue;
        }

        /* assumes in-order response IDs, good enough for now. */
        if (status == BLK_RESP_OK && id == done_request_id) {
            GAME_PRINT("Finished a playthrough\n");
            did_finish = true;
        }
    }

    if (did_fail) {
        GAME_PRINT("Errors encountered, stopping play.\n");
        is_playing = false;

        if (pending_eject) {
            pending_eject = false;
            hotplug_ready_for_eject(CHANNEL_HOTPLUG);
        }

        return;
    }

    if (did_finish) {
        if (pending_eject) {
            is_playing = false;
            pending_eject = false;
            hotplug_ready_for_eject(CHANNEL_HOTPLUG);
        } else if (blk_storage_is_ready(blk_storage_info)) {
            play_our_game();
        } else {
            is_playing = false;
            GAME_PRINT("Cannot continue the game\n");
        }
    }
}

void notified_blk_state(void)
{
    if (blk_storage_is_ready(blk_storage_info)) {
        GAME_PRINT("Storage ready!\n");
        if (!is_playing) {
            GAME_PRINT("playing...\n");
            play_our_game();
        }
    } else {
        GAME_PRINT("Storage is no longer ready\n");
        is_playing = false;
    }
}

void notified_hotplug(void)
{
    pending_eject = hotplug_is_pending_eject(hotplug_info);
    GAME_PRINT("Hotplug notify: pending eject...: %u\n", pending_eject);
    if (!is_playing) {
        GAME_PRINT("... wasn't playing, ACK.\n");
        hotplug_ready_for_eject(CHANNEL_HOTPLUG);
    }
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case CHANNEL_BLK_QUEUE:
        notified_blk_virt();
        break;

    case CHANNEL_BLK_STATE:
        notified_blk_state();
        break;

    case CHANNEL_HOTPLUG:
        notified_hotplug();
        break;

    default:
        assert(!"unknown channel");
    }
}

void init(void)
{
    /* The third partition on the SD card (after Uboot & Linux) is made empty
       so we don't overwrite anything important.
    */
    assert(blk_partition_mapping[0] == 2);

    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_SIZE_CLI0);
    GAME_PRINT("Hello!\n");

    /* continued via state notification */
}
