/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/serial/queue.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/usb/constants.h>
#include <sddf/usb/device.h>
#include <sddf/usb/report_queue.h>
#include <sddf/util/printf.h>

/* Uncomment this to enable debug logging */
// #define DEBUG_HID_VIRT

#if defined(DEBUG_HID_VIRT)
#define LOG_HID_VIRT(...) do{ sddf_dprintf("HID_VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#define REPORT_PERIOD 2000 * NS_IN_MS
#else
#define LOG_HID_VIRT(...) do{}while(0)
#endif
#define LOG_HID_VIRT_ERR(...) do{ sddf_dprintf("HID_VIRT|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

#ifndef REPORT_PERIOD
/* Should inspect bInterval, but 125 Hz is a safe starting point */
#define REPORT_PERIOD 8 * NS_IN_MS
#endif

static void process_kbd_report(hid_keyboard_report_t const *report);

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

static sddf_channel timer_channel;
static report_queue_handle_t hid_virt_qh;
static report_queue_handle_t client_report_qh;
static serial_queue_handle_t client_ascii_qh;
static const hid_device_t *hid = (hid_device_t *) HID_DEVICE_VADDR;

static uint8_t const keycode2ascii[128][2] = { HID_KEYCODE_TO_ASCII };
char *type[] = { "", "keyboard", "mouse" };
static hid_keyboard_report_t previous_keyboard_report = { 0 };
static hid_type_t current;

void init(void)
{
    (void) current;
    (void) hid;
    assert(timer_config_check_magic(&config));
    timer_channel = config.driver_id;

    report_queue_init(&hid_virt_qh,
                      (report_queue_t *) VIRT_REPORT_QUEUE_VADDR,
                      VIRT_REPORT_QUEUE_CAPACITY,
                      (hid_report_t *) VIRT_REPORT_DATA_VADDR);
    report_queue_init(&client_report_qh,
                      (report_queue_t *) CLIENT_REPORT_QUEUE_VADDR,
                      CLIENT_REPORT_QUEUE_CAPACITY,
                      (hid_report_t *) CLIENT_REPORT_DATA_VADDR);
    serial_queue_init(&client_ascii_qh,
                      (serial_queue_t *) CLIENT_ASCII_QUEUE_VADDR,
                      CLIENT_ASCII_QUEUE_CAPACITY,
                      (char *) CLIENT_ASCII_DATA_VADDR);
}

void notified(sddf_channel ch)
{
    if (ch == config.driver_id) {
        LOG_HID_VIRT("Requesting HID report\n");
        sddf_notify(USB_PROTOCOL_REQUEST_REPORT);
        sddf_timer_set_timeout(timer_channel, REPORT_PERIOD);
        return;
    }

    switch (ch) {
        case HID_VIRT_MOUNT: {
            LOG_HID_VIRT("A %s device has been mounted\n", type[hid->type]);
            sddf_timer_set_timeout(timer_channel, REPORT_PERIOD);
            sddf_notify(CLIENT_HID_MOUNT);
            break;
        }
        case HID_VIRT_UNMOUNT: {
            LOG_HID_VIRT("A %s device has been unmounted\n", type[current]);
            sddf_notify(CLIENT_HID_UNMOUNT);
            break;
        }
        case HID_VIRT_REPORT_AVAILABLE: {
            hid_report_t report;
            while (!report_dequeue(&hid_virt_qh, &report)) {
                if (report.type == KEYBOARD) {
                    process_kbd_report(&report.keyboard_report);
                    sddf_notify(CLIENT_HID_ASCII_AVAILABLE);
                }
                report_enqueue(&client_report_qh, report);
            }
            sddf_notify(CLIENT_HID_REPORT_AVAILABLE);
            break;
        }
        default: {
            LOG_HID_VIRT_ERR("Received unexpected notification from Channel %u\n", ch);
            break;
        }
    }
}

static inline
bool find_key_in_report(hid_keyboard_report_t const *report, uint8_t keycode) {
    for (int i = 0; i < NUM_KEYCODES; i++) {
        if (report->keycode[i] == keycode) {
            return true;
        }
    }

    return false;
}

static void
process_kbd_report(hid_keyboard_report_t const *report) {
    for (int i = 0; i < NUM_KEYCODES; i++) {
        bool is_keycode_null = !report->keycode[i];
        bool is_key_held = find_key_in_report(&previous_keyboard_report,
                                              report->keycode[i]);
        if (is_keycode_null || is_key_held) {
            continue;
        }

        bool const is_shift = report->modifier
                & (KEYBOARD_MODIFIER_LEFTSHIFT | KEYBOARD_MODIFIER_RIGHTSHIFT);
        uint8_t ch = keycode2ascii[report->keycode[i]][is_shift ? 1 : 0];

        if (ch != 0) {
            serial_enqueue(&client_ascii_qh, ch);
        }
    }

    previous_keyboard_report = *report;
}
