/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/printf.h>

__attribute__((__section__(".serial_client_config"))) serial_client_config_t config;

serial_queue_handle_t rx_queue_handle;
serial_queue_handle_t tx_queue_handle;

void init(void)
{
    assert(serial_config_check_magic(&config));

    serial_queue_init(&rx_queue_handle, config.rx.queue.vaddr, config.rx.data.size, config.rx.data.vaddr);
    serial_queue_init(&tx_queue_handle, config.tx.queue.vaddr, config.tx.data.size, config.tx.data.vaddr);

    serial_putchar_init(config.tx.id, &tx_queue_handle);
    sddf_printf("Hello world! I am %s\n", sddf_get_pd_name());
}

/**
 * Simple parsing state machine.
 * in release/press waiting for next char.
 *
 *         /-  press (1) -> reset
 *         -  release (2) -> reset
 *       /
 * reset (0)
 *       \  - mouse button release (3) -> reset.
 *        \ - mouse button release (4) -> reset.
 *
 */

typedef enum state {
    State_Reset = 0,
    State_KeyPress = 1,
    State_KeyRelease = 2,
    State_MouseKeyChange = 3,
    State_MouseMove = 4,
} state_t;

uint8_t mouse_move_count;
uint32_t dx;
uint32_t dy;
state_t state = State_Reset;
bool active_keys[128];
uint8_t buttonState = 0;

/**
 * Protocol:
 *
 * Each byte is 8 bits, the high bits indicates the start for self-synchronising.
 *    (reader can wait til the next high bit)
 *
 * This gives us 7 bits to work with in each byte.
 *
 * First byte (with the high bit) is the command.
 *  0x0: key press, following byte is (oem) key.
 *  0x1: key release, following byte is (oem) key
 *  0x2: mouse key press change (following is mouse buttons)
 *  0x3: mouse move (following is 10 bytes of 2x32 (dx then dy) bits int in 7 bits)
 *
 */

typedef enum cmd {
  Cmd_KeyPress = 0x0,
  Cmd_KeyRelease = 0x1,
  Cmd_MouseKeyChange = 0x2,
  Cmd_MouseMove = 0x3,
} cmd_t;

enum MouseButton {
  LEFT_BUTTON   = 0x01,
  MIDDLE_BUTTON = 0x02,
  RIGHT_BUTTON  = 0x04
};

void notified(sddf_channel ch)
{
    uint8_t c;
    while (!serial_dequeue(&rx_queue_handle, (char *)&c)) {
        // sddf_dprintf("got char: '%x'\n", c);

        switch (state) {
        case State_Reset:
            /* high bit set == command */
            if (c & BIT(7)) {
                c &= ~BIT(7);
                switch ((cmd_t)c) {
                case Cmd_KeyPress:
                    state = State_KeyPress;
                    break;
                case Cmd_KeyRelease:
                    state = State_KeyRelease;
                    break;
                case Cmd_MouseKeyChange:
                    state = State_MouseKeyChange;
                    break;
                case Cmd_MouseMove:
                    state = State_MouseMove;
                    mouse_move_count = 0;
                    dx = 0;
                    dy = 0;
                    break;

                default:
                    sddf_dprintf("unknown command: '%d'", c);
                    break;
                }
            } else {
                sddf_dprintf("waiting for sync..., ignoring\n");
            }

            break;

        case State_KeyPress:
            if (c & BIT(7)) {
                state = State_Reset;
                sddf_dprintf("got command following command, protocol violation\n");
                break;
            }

            active_keys[c] = true;
            state = State_Reset;
            sddf_dprintf("pressed key '%d'\n", c);
            break;

        case State_KeyRelease:
            if (c & BIT(7)) {
                state = State_Reset;
                sddf_dprintf("got command following command, protocol violation\n");
                break;
            }

            active_keys[c] = false;
            state = State_Reset;
            sddf_dprintf("released key '%d'\n", c);
            break;

        case State_MouseKeyChange:
            if (c & BIT(7)) {
                state = State_Reset;
                sddf_dprintf("got command following command, protocol violation\n");
                break;
            }

            state = State_Reset;
            buttonState = c;
            sddf_dprintf("pressed mouse '%d':", c);
            if (buttonState & LEFT_BUTTON) {
                sddf_dprintf(" left button");
            }
            if (buttonState & MIDDLE_BUTTON) {
                sddf_dprintf(" middle button");
            }
            if (buttonState & RIGHT_BUTTON) {
                sddf_dprintf(" right button");
            }
            sddf_dprintf("\n");
            break;

        case State_MouseMove:
            if (c & BIT(7)) {
                state = State_Reset;
                sddf_dprintf("got command following command, protocol violation\n");
                break;
            }


            uint32_t v = c;
            /* first five is dx (0-4) */
            if (mouse_move_count < 5) {
                uint8_t i = 7 * (mouse_move_count);
                dx |= (v << i);
            } else { /* rest (5-9) is dy */
                uint8_t i = 7 * (mouse_move_count - 5);
                dy |= (v << i);
            }

            mouse_move_count += 1;
            if (mouse_move_count == 10) {
                sddf_dprintf("mouse move: dx=%d,dy=%d\n", dx, dy);
                state = State_Reset;
            }
            break;

        default:
            assert(!"unknown state\n");
        }
    }
}
