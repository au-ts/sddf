/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <class/hid/hid.h>
#include <class/msc/msc.h>

typedef enum {
    NONE = 0,
    KEYBOARD = 1,
    MOUSE = 2
} hid_type_t;

typedef union hid_report_payload {
    hid_keyboard_report_t keyboard_report;
    hid_mouse_report_t mouse_report;
} hid_report_payload_t;

typedef struct hid_report {
    hid_type_t type;
    union {
        hid_keyboard_report_t keyboard_report;
        hid_mouse_report_t mouse_report;
    };
} hid_report_t;

typedef struct hid_device {
    bool connected;
    uint8_t daddr;
    uint8_t instance;
    hid_type_t type;
} hid_device_t;

typedef struct msc_device {
    bool connected;
    uint8_t daddr;
    uint8_t lun;
    uint32_t block_count;
    uint32_t block_size;
    scsi_inquiry_resp_t inquiry_resp;
    bool inquiry_in_progress;
    bool inquiry_succeeded;
} msc_device_t;

static inline void print_msc_inquiry(const msc_device_t *msc)
{
    sddf_printf("    %.8s %.16s rev %.4s\n", msc->inquiry_resp.vendor_id,
                msc->inquiry_resp.product_id, msc->inquiry_resp.product_rev);
    sddf_printf("    Disk size: %u MB\n",
                msc->block_count / ((1024 * 1024) / msc->block_size));
    sddf_printf("    Block count: %u; Block size: %u\n",
                msc->block_count, msc->block_size);
}
