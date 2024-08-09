#include <stdint.h>
#include <microkit.h>
#include <sddf/blk/queue.h>
#include <sddf/hotplug/hotplug.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

#include "blk_config.h"

#define CHANNEL_BLK_VIRT 0
#define CHANNEL_HOTPLUG  1

blk_queue_handle_t blk_queue;
blk_storage_info_t *blk_config;
blk_req_queue_t *blk_req_queue;
blk_resp_queue_t *blk_resp_queue;
uint8_t *blk_data;

hotplug_shared_device_t *block_device;

static uint32_t request_id = 0;
static uint32_t done_request_id;
static bool is_playing = true;

#define GAME_PRINT(...) do{ sddf_printf("GAME: "); sddf_printf(__VA_ARGS__); }while(0)

void play_our_game_stage(uint8_t stage)
{
    for (int i = 0; i < BLK_TRANSFER_SIZE; i++) {
        blk_data[i] = stage;
    }
}

void play_our_game(void)
{
    is_playing = true;

    int err;
    for (int stage = UINT8_MAX - 20; stage < UINT8_MAX; stage++) {
        play_our_game_stage(stage);
        err = blk_enqueue_req(&blk_queue, BLK_REQ_WRITE, /* data offset */ 0x0,
                                  /* block number */ 0x0, /* block count */ 0x1, request_id++);
        assert(!err);

        /* not strictly necessary, but let's do this anyway */
        err = blk_enqueue_req(&blk_queue, BLK_REQ_FLUSH, 0, 0, 0, request_id++);
        assert(!err);

        microkit_notify(CHANNEL_BLK_VIRT);
    }

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
            GAME_PRINT("Received a non-successful queue response...\n");
            GAME_PRINT("-> status: %u, count: %u, id: %u\n", status, success_count, id);
            did_fail = true;
            continue;
        }

        /* assumes in-order response IDs, good enough for now. */
        if (status == BLK_RESP_OK && id == done_request_id) {
            GAME_PRINT("Finished a playthrough\n");
            did_finish = true;
        }
    }

    if (did_fail) {
        GAME_PRINT("Errors encountered, stopping play.");
        is_playing = false;
        return;
    }

    if (did_finish) {
        uint8_t state = __atomic_load_n(&block_device->state, __ATOMIC_ACQUIRE);
        if (state == SDDF_HOTPLUG_STATE_INSERTED) {
            play_our_game();
        } else if (state == SDDF_HOTPLUG_STATE_EJECTING) {
            is_playing = false;
            sddf_hotplug_notify(CHANNEL_HOTPLUG, block_device, SDDF_HOTPLUG_STATE_OK_TO_EJECT);
        } else if (state == SDDF_HOTPLUG_STATE_EJECTED) {
            /* we were force ejected */
            is_playing = false;
            GAME_PRINT("force ejected\n");
        } else {
            GAME_PRINT("Unexpected state: %u\n", state);
        }
    }
}

void notified_hotplug(void)
{
    GAME_PRINT("Hotplug state notification!\n");

    switch (__atomic_load_n(&block_device->state, __ATOMIC_ACQUIRE)) {
        case SDDF_HOTPLUG_STATE_INSERTED:
            GAME_PRINT("-> Now inserted\n");
            if (!is_playing) {
                play_our_game();
            }
            break;

        case SDDF_HOTPLUG_STATE_EJECTING:
            GAME_PRINT("-> Wanting unmount\n");
            break;

        case SDDF_HOTPLUG_STATE_OK_TO_EJECT:
            GAME_PRINT("-> OK to unmount (well we shouldn't ever see this one)\n");
            break;

        case SDDF_HOTPLUG_STATE_EJECTED:
            GAME_PRINT("-> Card unmounted!\n");
            break;
    }
}

void notified(microkit_channel ch)
{
    switch (ch) {
    case CHANNEL_BLK_VIRT:
        return notified_blk_virt();

    case CHANNEL_HOTPLUG:
        return notified_hotplug();

    default:
        assert(!"unknown channel");
    }
}

void init(void)
{
    blk_queue_init(&blk_queue, blk_req_queue, blk_resp_queue, BLK_QUEUE_SIZE_CLI0);

    /* Busy wait until blk device is ready */
    while (!__atomic_load_n(&blk_config->ready, __ATOMIC_ACQUIRE));

    GAME_PRINT("Hello!\n");

    /* The third partition on the SD card (after Uboot & Linux) is made empty
       so we don't overwrite anything important.
    */
    assert(blk_partition_mapping[0] == 2);

    play_our_game();
}
