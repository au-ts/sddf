/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/input/input.h>
#include <sddf/input/evdev.h>
#include <sddf/util/printf.h>

#define LV_LVGL_H_INCLUDE_SIMPLE

#include "lvgl/lvgl.h"

#define RESX 600
#define RESY 400

#define TFT_HOR_RES RESX
#define TFT_VER_RES RESY

uint8_t *fb_address;

#include "ramfb.h"

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

struct input_event_queue *keyboard_events = (struct input_event_queue *)0x10000000;
struct input_event_queue *mouse_events = (struct input_event_queue *)0x20000000;

#define KEYBOARD_CH 0
#define MOUSE_CH 1

float mouse_x;
float mouse_y;

bool clicked = false;

void notified(sddf_channel ch)
{
    if (ch == MOUSE_CH) {
        for (int i = 0; i < mouse_events->n; i++) {
            struct virtio_input_event event = mouse_events->events[i];
            if (event.type == EV_KEY && event.code == BTN_MOUSE) {
                sddf_dprintf("CLIENT: got click! (%d, %d, %d)\n", event.type, event.code, event.value);
                clicked = event.value == 1;
            }
            if (event.type == EV_ABS) {
                if (event.code == ABS_X) {
                    mouse_x = (float)event.value * ((float)RESX / (float)32767);
                }
                if (event.code == ABS_Y) {
                    mouse_y = (float)event.value * ((float)RESY / (float)32767);
                }
            }
        }
    }

    lv_timer_handler();
    if (ch == config.driver_id) {
        sddf_timer_set_timeout(config.driver_id, NS_IN_MS * 5);
    }
}

static void pointer_input_cb(lv_indev_t * indev, lv_indev_data_t * data)
{
    if (clicked) {
        data->point.x = mouse_x;
        data->point.y = mouse_y;
        data->state = LV_INDEV_STATE_PRESSED;
    } else {
        data->state = LV_INDEV_STATE_RELEASED;
    }
}

static uint32_t tick_cb(void)
{
    uint64_t time = sddf_timer_time_now(config.driver_id);
    return time / NS_IN_MS;
}

static void flush_cb(lv_display_t * disp, const lv_area_t * area, uint8_t * px_map)
{
    /*Write px_map to the area->x1, area->x2, area->y1, area->y2 area of the
     *frame buffer or external display controller. */
    sddf_dprintf("flush_cb called, area: x1: %d, y1: %d, x2: %d, y2: %d\n", area->x1, area->y1, area->x2, area->y2);

    // TODO: do properly
    size_t fb_off = RESX * (area->y1 + 1) * 4;
    size_t n = 20;

    size_t nbytes = n * RESX * 4;
    sddf_dprintf("copying to [0x%lx..0x%lx) from [0x%lx..0x%lx)\n", fb_address + fb_off, fb_address + fb_off + nbytes, px_map, px_map + nbytes);
    memcpy((uint8_t *)fb_address + fb_off, px_map, nbytes);

    sddf_dprintf("flush_cb finish?\n");
    /* signal LVGL that we're done */
    lv_display_flush_ready(disp);
}

void draw_ui(void)
{
    /*Initialize LVGL*/
    lv_init();

    /*Set millisecond-based tick source for LVGL so that it can track time.*/
    lv_tick_set_cb(tick_cb);

    /*Create a display where screens and widgets can be added*/
    lv_display_t * display = lv_display_create(TFT_HOR_RES, TFT_VER_RES);

    /*Add rendering buffers to the screen.
     *Here adding a smaller partial buffer assuming 16-bit (RGB565 color format)*/
    static uint8_t buf[TFT_HOR_RES * TFT_VER_RES / 10 * 2]; /* x2 because of 16-bit color depth */
    lv_display_set_buffers(display, buf, NULL, sizeof(buf), LV_DISPLAY_RENDER_MODE_PARTIAL);

    /*Add a callback that can flush the content from `buf` when it has been rendered*/
    lv_display_set_flush_cb(display, flush_cb);

    /*Create an input device for touch handling*/
    lv_indev_t * indev = lv_indev_create();
    lv_indev_set_type(indev, LV_INDEV_TYPE_POINTER);
    lv_indev_set_read_cb(indev, pointer_input_cb);

    /*The drivers are in place; now we can create the UI*/
    // lv_obj_t * label = lv_label_create(lv_screen_active());
    // lv_label_set_text(label, "Hello world");
    // lv_obj_center(label);

    lv_obj_t *sw = lv_switch_create(lv_screen_active());
    lv_obj_center(sw);
    lv_obj_add_state(sw, LV_STATE_CHECKED);
    // lv_obj_add_event_cb(sw, sw_event_cb, LV_EVENT_VALUE_CHANGED, label);

    sddf_timer_set_timeout(config.driver_id, NS_IN_MS * 5);
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");

    assert(timer_config_check_magic(&config));

    struct QemuRamFBCfg cfg;
    qemu_ramfb_make_cfg(&cfg, (void *)DMA_ADDRESS_PADDR, RESX, RESY);
    qemu_ramfb_configure(&cfg);

    fb_address = (uint8_t*)DMA_ADDRESS_VADDR;
    for (int i = 0; i < RESY * RESX * 4; i++) {
        fb_address[i] = 0xff;
    }

    draw_ui();
}
