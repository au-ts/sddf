/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>

struct virtio_input_event {
    uint16_t type;
    uint16_t code;
    uint32_t value;
};

struct virtio_input_event *keyboard_events = (struct virtio_input_event *)0x10000000;
struct virtio_input_event *mouse_events = (struct virtio_input_event *)0x20000000;

#define KEYBOARD_CH 0
#define MOUSE_CH 1

void notified(sddf_channel ch)
{
    assert(ch == KEYBOARD_CH || ch == MOUSE_CH);
    if (KEYBOARD_CH) {
        sddf_printf("CLIENT|INFO: keyboard event\n");
        sddf_printf("event type: 0x%x, code: 0x%x, value: 0x%lx\n", keyboard_events->type, keyboard_events->code, keyboard_events->value);
    } else {
        sddf_printf("CLIENT|INFO: mouse event\n");
        sddf_printf("event type: 0x%x, code: 0x%x, value: 0x%lx\n", mouse_events->type, mouse_events->code, mouse_events->value);
    }
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");
}
