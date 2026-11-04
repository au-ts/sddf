/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <os/sddf.h>
#include <sddf/serial/config.h>
#include <sddf/usb/constants.h>
#include <sddf/usb/report_queue.h>
#include <sddf/usb/device.h>
#include <sddf/util/printf.h>
#include <class/hid/hid.h>
#include <class/msc/msc.h>

#define LOG_CLIENT(...) do{ sddf_printf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#define LOG_CLIENT_ERR(...) do{ sddf_printf("CLIENT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define NUM_KEYCODES 6

static void request_msc_inquiry(void);
static inline bool find_key_in_report(hid_keyboard_report_t const *report, uint8_t keycode);
static void process_kbd_report(hid_keyboard_report_t const *report);
static void process_mouse_report(hid_mouse_report_t const *report);

static report_queue_handle_t report_qh;
static serial_queue_handle_t ascii_qh;
static const msc_device_t *msc = (msc_device_t *) MSC_DEVICE_VADDR;
static const hid_device_t *hid = (hid_device_t *) HID_DEVICE_VADDR;

static uint8_t const keycode2ascii[128][2] = { HID_KEYCODE_TO_ASCII };
static char *type[] = { "none", "keyboard", "mouse" };
static bool show_report = true;
static bool show_ascii = false;
static hid_type_t current_hid_type = NONE;
static hid_keyboard_report_t previous_keyboard_report = { 0 };

void init(void)
{
    LOG_CLIENT("Starting...\n");
    report_queue_init(&report_qh,
                      (report_queue_t *) CLIENT_REPORT_QUEUE_VADDR,
                      CLIENT_REPORT_QUEUE_CAPACITY,
                      (hid_report_t *) CLIENT_REPORT_DATA_VADDR);
    serial_queue_init(&ascii_qh,
                      (serial_queue_t *) CLIENT_ASCII_QUEUE_VADDR,
                      CLIENT_ASCII_QUEUE_CAPACITY,
                      (char *) CLIENT_ASCII_DATA_VADDR);
}

void notified(sddf_channel ch)
{
    switch (ch) {
        case CLIENT_MSC_MOUNT: {
            LOG_CLIENT("A mass storage device has been mounted\n");
            request_msc_inquiry();
            break;
        }
        case CLIENT_MSC_UNMOUNT: {
            LOG_CLIENT("A mass storage device has been unmounted\n");
            break;
        }
        case CLIENT_HID_MOUNT: {
            LOG_CLIENT("A %s device has been mounted\n", type[hid->type]);
            current_hid_type = hid->type;
            break;
        }
        case CLIENT_HID_UNMOUNT: {
            LOG_CLIENT("A %s device has been unmounted\n",
                       type[current_hid_type]);
            current_hid_type = NONE;
            show_ascii = false;
            show_report = true;
            break;
        }
        case CLIENT_HID_ASCII_AVAILABLE: {
            char c;
            while (!serial_dequeue(&ascii_qh, &c)) {
                if (show_ascii) {
                    LOG_CLIENT("%c\n", c);
                }
            }
            break;
        }
        case CLIENT_HID_REPORT_AVAILABLE: {
            hid_report_t report;
            while (!report_dequeue(&report_qh, &report)) {
                if (hid->type == KEYBOARD) {
                    process_kbd_report(&report.keyboard_report);
                } else if (hid->type == MOUSE) {
                    process_mouse_report(&report.mouse_report);
                }
            }
            break;
        }
        default:
            LOG_CLIENT_ERR("Received unexpected notification from channel %u\n",
                           ch);
            break;
    }
}

static void request_msc_inquiry(void) {
    if (msc->connected) {
        seL4_MessageInfo_t msg = seL4_MessageInfo_new(CLIENT_MSC_INQUIRY, 0, 0, 0);
        msg = sddf_ppcall(CLIENT_MSC_PPC, msg);
        if (seL4_MessageInfo_get_label(msg) == SUCCESS) {
            print_msc_inquiry(msc);
        } else {
            LOG_CLIENT_ERR("MSC inquiry failed\n");
        }
    } else {
        LOG_CLIENT("Inquiry failed: No mass storage device is connected\n");
    }
}

static inline
bool find_key_in_report(hid_keyboard_report_t const *report, uint8_t keycode)
{
    for (int i = 0; i < NUM_KEYCODES; i++) {
        if (report->keycode[i] == keycode) {
            return true;
        }
    }

    return false;
}

static
void process_kbd_report(hid_keyboard_report_t const *report) {
    for (int i = 0; i < NUM_KEYCODES; i++) {
        bool is_keycode_null = !report->keycode[i];
        bool is_key_held = find_key_in_report(&previous_keyboard_report,
                                              report->keycode[i]);
        
        if (is_keycode_null || is_key_held) {
            continue;
        }

        bool const is_shift = report->modifier
                & (KEYBOARD_MODIFIER_LEFTSHIFT | KEYBOARD_MODIFIER_RIGHTSHIFT);
        bool const is_ctrl = report->modifier
                & (KEYBOARD_MODIFIER_LEFTCTRL | KEYBOARD_MODIFIER_RIGHTCTRL);

        /* Toggle output mode on <CTRL-T> */
        if (is_ctrl && report->keycode[i] == HID_KEY_T) {
            show_report = !show_report;
            show_ascii = !show_ascii;
        }

        if (show_report) {
            LOG_CLIENT("Keyboard HID report received\n");
            sddf_printf("    Modifiers:\t0x%02x\t %s%s%s%s%s%s%s%s%s\n",
                        report->modifier,
                        !report->modifier           ? "<None>"          : "",
                        (report->modifier & BIT(0)) ? "<LeftControl> "  : "",
                        (report->modifier & BIT(1)) ? "<LeftShift> "    : "",
                        (report->modifier & BIT(2)) ? "<LeftAlt> "      : "",
                        (report->modifier & BIT(3)) ? "<LeftGUI> "      : "",
                        (report->modifier & BIT(4)) ? "<RightControl> " : "",
                        (report->modifier & BIT(5)) ? "<RightShift> "   : "",
                        (report->modifier & BIT(6)) ? "<RightAlt> "     : "",
                        (report->modifier & BIT(7)) ? "<RightGUI> "     : "");
            sddf_printf("    Keycode:\t0x%02x\t%c\n", report->keycode[i],
                        keycode2ascii[report->keycode[i]][is_shift ? 1 : 0]);
        }
    }

    previous_keyboard_report = *report;
}

static
void process_mouse_report(hid_mouse_report_t const *report)
{
    LOG_CLIENT("Mouse HID report received\n");
    sddf_printf("    Buttons:\t0x%02x\t %s%s%s%s%s%s\n",
                report->buttons,
                !report->buttons           ? "<None>"            : "",
                (report->buttons & BIT(0)) ? "<ButtonLeft> "     : "",
                (report->buttons & BIT(1)) ? "<ButtonRight> "    : "",
                (report->buttons & BIT(2)) ? "<ButtonMiddle> "   : "",
                (report->buttons & BIT(3)) ? "<ButtonBackward> " : "",
                (report->buttons & BIT(4)) ? "<ButtonForward> "  : "");
    sddf_printf("    X offset:\t%d\n", report->x);
    sddf_printf("    Y offset:\t%d\n", report->y);
}
