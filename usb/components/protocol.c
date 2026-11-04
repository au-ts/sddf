/*
 * The USB host example source code was obtained from TinyUSB's examples; it is
 * licensed under the MIT License and is Copyright (c) 2019-2025, hatach
 * (tinyusb.org).
 * 
 * All other source code has a BSD 2-Clause License and is Copyright 2025, UNSW.
 * 
 * SPDX-License-Identifier: BSD-2-Clause AND MIT
 */

#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/usb/constants.h>
#include <sddf/usb/device.h>
#include <sddf/usb/event_queue.h>
#include <sddf/usb/report_queue.h>
#include <sddf/util/cache.h>
#include <sddf/util/printf.h>
#include <bsp/board_api.h>

/* Uncomment this to enable debug logging */
// #define DEBUG_USB_PROTOCOL

#if defined(DEBUG_USB_PROTOCOL)
#define LOG_USB(...) do{ sddf_dprintf("USB PROTOCOL|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_USB(...) do{}while(0)
#endif
#define LOG_USB_ERR(...) do{ sddf_dprintf("USB PROTOCOL|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

static bool wait_for_inquiry(uint8_t dev_addr, tuh_msc_complete_data_t const *cb_data);

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

sddf_channel timer_channel;
static sddf_channel usb_driver_channel;
static event_queue_handle_t event_qh;
report_queue_handle_t hid_virt_qh;
static hid_device_t *hid = (hid_device_t *) HID_DEVICE_VADDR;
static msc_device_t *msc = (msc_device_t *) MSC_DEVICE_VADDR;

static
bool wait_for_inquiry(uint8_t dev_addr, tuh_msc_complete_data_t const *cb_data)
{
    msc_csw_t const *csw = cb_data->csw;
    if (csw->status == 0) {
        msc->inquiry_succeeded = true;
    } else {
        msc->inquiry_succeeded = false;
    }

    msc->inquiry_in_progress = false;
    return msc->inquiry_succeeded;
}

void init(void)
{
    usb_driver_channel = 0;
    assert(timer_config_check_magic(&config));
    timer_channel = config.driver_id;

    event_queue_init(&event_qh, (event_queue_t *) EVENT_QUEUE_VADDR,
                     EVENT_QUEUE_CAPACITY, (hcd_event_t *) EVENT_DATA_VADDR);
    report_queue_init(&hid_virt_qh, (report_queue_t *) VIRT_REPORT_QUEUE_VADDR,
                      VIRT_REPORT_QUEUE_CAPACITY,
                      (hid_report_t *) VIRT_REPORT_DATA_VADDR);

    LOG_USB("Starting...\n");
    board_init();

    tusb_rhport_init_t host_init = {
        .role = TUSB_ROLE_HOST,
        .speed = TUSB_SPEED_AUTO
    };
    tusb_init(BOARD_TUH_RHPORT, &host_init);
}

void notified(sddf_channel ch)
{
    if (ch == usb_driver_channel || ch == timer_channel) {
        hcd_event_t event;
        while (!event_dequeue(&event_qh, &event)) {
            tuh_queue_event(&event);
        }
        tuh_task();
    } else if (ch == HID_VIRT_REPORT_REQUEST) {
        if (hid->connected) {
            if (tuh_hid_receive_ready(hid->daddr, 0)) {
                tuh_hid_receive_report(hid->daddr, 0);
            }
        }
    } else {
        LOG_USB_ERR("Received unexpected notification from Channel %u\n", ch);
    }
}


seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    bool success = false;

    switch (seL4_MessageInfo_get_label(msginfo)) {
        case MSC_VIRT_INQUIRY: {
            if (!msc->connected) {
                LOG_USB_ERR("No mass-storage device is conncected\n");
                break;
            }

            msc->inquiry_in_progress = true;
            tuh_msc_inquiry(msc->daddr, msc->lun, &msc->inquiry_resp,
                            wait_for_inquiry, 0);

            /* Continue to process events while we wait for the inquiry */
            while (msc->inquiry_in_progress) {
                hcd_event_t event;

                if (!event_dequeue(&event_qh, &event)) {
                    tuh_queue_event(&event);
                }

                tuh_task();
            }

            success = msc->inquiry_succeeded;
            break;
        }
        default: {
            LOG_USB_ERR("Received unknown PPC request\n");
            break;
        }
    }

    return seL4_MessageInfo_new(success, 0, 0, 0);
}

void tuh_mount_cb(uint8_t dev_addr)
{
    TU_LOG1("A device with address %u has been mounted\n", dev_addr);
}

void tuh_umount_cb(uint8_t dev_addr)
{
    TU_LOG1("A device with address %u has been unmounted\n", dev_addr);
}

/* Mass-storage devices */

/**
 * Invoked when a mass-storage device has been mounted
 */
void tuh_msc_mount_cb(uint8_t dev_addr)
{
    if (msc->connected) {
        return;
    }

    TU_LOG1("A mass storage device with address %u has been mounted\n",
            dev_addr);

    msc->connected = true;
    msc->daddr = dev_addr;
    msc->lun = 0;
    msc->block_count = tuh_msc_get_block_count(dev_addr, msc->lun);
    msc->block_size = tuh_msc_get_block_size(dev_addr, msc->lun);
    msc->inquiry_in_progress = false;
    msc->inquiry_succeeded = false;
    sddf_notify(VIRT_MSC_MOUNT);
}

/**
 * Invoked when a mass-storage device has been unmounted
 */
void tuh_msc_umount_cb(uint8_t dev_addr)
{
    if (msc->connected && msc->daddr != dev_addr) {
        return;
    }

    TU_LOG1("A mass storage device with address %u has been unmounted\n",
            dev_addr);

    msc->connected = false;
    msc->daddr = TUSB_INDEX_INVALID_8;
    sddf_notify(VIRT_MSC_UNMOUNT);
}

/* Human-interface devices */

/**
 * Invoked when a human-interface device has been mounted
 */
void tuh_hid_mount_cb(uint8_t dev_addr, uint8_t instance,
                      uint8_t const *desc_report, uint16_t desc_len)
{
    if (!hid->connected && instance == 0) {
        TU_LOG1("HID device address = %d, instance = %d is mounted\n",
                dev_addr, instance);
        hid->connected = true;
        hid->daddr = dev_addr;
        hid->instance = instance;
        hid->type = tuh_hid_interface_protocol(dev_addr, instance);
        sddf_notify(HID_VIRT_MOUNT);
    }
}

/**
 * Invoked when a human-interface device has been unmounted
 */
void tuh_hid_umount_cb(uint8_t dev_addr, uint8_t instance)
{
    if (hid->connected && hid->daddr == dev_addr && hid->instance == instance) {
        TU_LOG1("HID device address = %d, instance = %d is unmounted\n",
                dev_addr, instance);
        hid->connected = false;
        hid->daddr = TUSB_INDEX_INVALID_8;
        hid->type = TUSB_INDEX_INVALID_8;
        sddf_notify(HID_VIRT_UNMOUNT);
    }
}

/**
 * Invoked when a human-interface device report has been received
 */
void tuh_hid_report_received_cb(uint8_t dev_addr, uint8_t instance,
                                uint8_t const *report, uint16_t len)
{
    uint8_t const itf_protocol = tuh_hid_interface_protocol(dev_addr, instance);
    hid_report_t hid_report;

    switch (itf_protocol) {
        case HID_ITF_PROTOCOL_KEYBOARD: {
            hid_report.type = KEYBOARD;
            hid_report.keyboard_report = *((hid_keyboard_report_t *) report);
            report_enqueue(&hid_virt_qh, hid_report);
            break;
        }
        case HID_ITF_PROTOCOL_MOUSE: {
            hid_report.type = MOUSE;
            hid_report.mouse_report = *((hid_mouse_report_t *) report);
            report_enqueue(&hid_virt_qh, hid_report);
            break;
        }
        default: {
            break;
        }
    }

    sddf_notify(HID_VIRT_REPORT_AVAILABLE);
}

/* Host timer API */

uint32_t board_millis(void)
{
    return sddf_timer_time_now(timer_channel) / NS_IN_MS;
}

uint32_t tusb_time_millis_api(void)
{
    return board_millis();
}

/* Host cache API */

void data_clean(volatile void *starting_address, size_t size)
{
    unsigned long start = (unsigned long) starting_address;
    unsigned long end = (unsigned long) starting_address + size;
    cache_clean(start, end);
}

void data_clean_and_invalidate(volatile void *starting_address, size_t size)
{
    unsigned long start = (unsigned long) starting_address;
    unsigned long end = (unsigned long) starting_address + size;
    cache_clean_and_invalidate(start, end);
}

void data_invalidate(volatile void *starting_address, size_t size)
{
    unsigned long start = (unsigned long) starting_address;
    unsigned long end = (unsigned long) starting_address + size;
    cache_clean_and_invalidate(start, end);
}
