/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/printf.h>
#include <sddf/input/input.h>

struct input_event_queue *keyboard_events = (struct input_event_queue *)0x10000000;
struct input_event_queue *mouse_events = (struct input_event_queue *)0x20000000;

#define KEYBOARD_CH 0
#define MOUSE_CH 1

void notified(sddf_channel ch)
{
    assert(ch == KEYBOARD_CH || ch == MOUSE_CH);
    if (ch == KEYBOARD_CH) {
        sddf_printf("CLIENT|INFO: keyboard event\n");
        for (int i = 0; i < keyboard_events->n; i++) {
            sddf_printf("event type: 0x%x, code: 0x%x, value: 0x%lx\n", keyboard_events->events[i].type, keyboard_events->events[i].code, keyboard_events->events[i].value);
        }
    } else {
        sddf_printf("CLIENT|INFO: mouse events:\n");
        for (int i = 0; i < mouse_events->n; i++) {
            sddf_printf("event type: 0x%x, code: 0x%x, value: 0x%lx\n", mouse_events->events[i].type, mouse_events->events[i].code, mouse_events->events[i].value);
        }
    }
}

void init(void)
{
    sddf_printf("CLIENT|INFO: starting\n");
}
