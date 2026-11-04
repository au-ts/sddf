/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/util/printf.h>
#include <sddf/usb/constants.h>
#include <sddf/usb/event_queue.h>

#include "usb.h"

#define DEV(dest) (dest >> CHAR_BIT)
#define EP(dest)  (dest & 0xFF)

static usbh_data_t *_usbh_data = (usbh_data_t*) _USBH_DATA_VADDR;
static usbh_device_t *_usbh_devices = (usbh_device_t*) _USBH_DEVICES_VADDR;
static event_queue_handle_t event_qh;

void init(void)
{
    event_queue_init(&event_qh, (event_queue_t *) EVENT_QUEUE_VADDR,
                     EVENT_QUEUE_CAPACITY,  (hcd_event_t *) EVENT_DATA_VADDR);
}

void notified(sddf_channel ch)
{
    hcd_int_handler(0, true);
    sddf_irq_ack(ch);
}

seL4_MessageInfo_t protected(sddf_channel ch, seL4_MessageInfo_t msginfo)
{
    bool success = true;
    uintptr_t ret_val = 0;
    uint8_t rhport = sddf_get_mr(RHPORT);

    switch (seL4_MessageInfo_get_label(msginfo)) {
        case HCD_CONFIGURE: {
            success = hcd_configure(rhport, sddf_get_mr(CFG_ID), NULL);
            break;
        }
        case HCD_INIT: {
            tusb_rhport_init_t rh_init;
            rh_init.role = sddf_get_mr(RH_ROLE);
            rh_init.speed = sddf_get_mr(RH_SPEED);
            success = hcd_init(rhport, &rh_init);
            break;
        }
        case HCD_INT_HANDLER: {
            hcd_int_handler(rhport, sddf_get_mr(IN_ISR));
            break;
        }
        case HCD_INT_ENABLE: {
            hcd_int_enable(rhport);
            break;
        }
        case HCD_INT_DISABLE: {
            hcd_int_disable(rhport);
            break;
        }
        case HCD_FRAME_NUMBER: {
            ret_val = hcd_frame_number(rhport);
            break;
        }
        case HCD_PORT_CONNECT_STATUS: {
            success = hcd_port_connect_status(rhport);
            break;
        }
        case HCD_PORT_RESET: {
            hcd_port_reset(rhport);
            break;
        }
        case HCD_PORT_RESET_END: {
            hcd_port_reset_end(rhport);
            break;
        }
        case HCD_PORT_SPEED_GET: {
            ret_val = hcd_port_speed_get(rhport);
            break;
        }
        case HCD_DEVICE_CLOSE: {
            hcd_device_close(rhport, (uint8_t) sddf_get_mr(DEV_ADDR));
            break;
        }
        case HCD_EDPT_OPEN: {
            uint8_t ep_desc[8];
            uint32_t hi = sddf_get_mr(EP_DESC_HI);
            uint32_t lo = sddf_get_mr(EP_DESC_LO);
            memcpy(ep_desc, &hi, sizeof(hi));
            memcpy(ep_desc + sizeof(hi), &lo, sizeof(lo));
            success = hcd_edpt_open(rhport, (uint8_t) sddf_get_mr(DEV_ADDR),
                                            (tusb_desc_endpoint_t *) ep_desc);
            break;
        }
        case HCD_EDPT_CLOSE: {
            success = hcd_edpt_close(rhport, (uint8_t) sddf_get_mr(DEV_ADDR),
                                             (uint8_t) sddf_get_mr(EP_ADDR));
            break;
        }
        case HCD_EDPT_XFER: {
            success = hcd_edpt_xfer(rhport, (uint8_t) DEV(sddf_get_mr(DEST)),
                                            (uint8_t) EP(sddf_get_mr(DEST)),
                                            (uint8_t *) sddf_get_mr(BUFFER),
                                            (uint16_t) sddf_get_mr(BUFLEN));
            break;
        }
        case HCD_EDPT_ABORT_XFER: {
            success = hcd_edpt_abort_xfer(rhport,
                                          (uint8_t) sddf_get_mr(DEV_ADDR),
                                          (uint8_t) sddf_get_mr(EP_ADDR));
            break;
        }
        case HCD_SETUP_SEND: {
            uint8_t setup_packet[8];
            uint32_t hi = sddf_get_mr(SETUP_HI);
            uint32_t lo = sddf_get_mr(SETUP_LO);
            memcpy(setup_packet, &hi, sizeof(hi));
            memcpy(setup_packet + sizeof(hi), &lo, sizeof(lo));
            success = hcd_setup_send(rhport, (uint8_t) sddf_get_mr(DEV_ADDR), 
                                     setup_packet);
            break;
        }
        case HCD_EDPT_CLEAR_STALL: {
            success = hcd_edpt_clear_stall(rhport,
                                           (uint8_t) sddf_get_mr(DEV_ADDR),
                                           (uint8_t) sddf_get_mr(EP_ADDR));
            break;
        }
        default: {
            sddf_dprintf("USB DRIVER|ERROR: Unknown request from Channel %u",
                         ch);
            break;
        }
    }

    seL4_MessageInfo_t msg = seL4_MessageInfo_new(success, 0, 0, 1);
    sddf_set_mr(RET_VAL, ret_val);
    return msg;
}

/* Pretend we're still talking directly to the protocol stack */

void hcd_event_handler(hcd_event_t const* event, bool in_isr)
{
    switch (event->event_id) {
        case HCD_EVENT_DEVICE_ATTACH:
        case HCD_EVENT_DEVICE_REMOVE: {
            if (event->connection.hub_addr == 0) {
                if (tu_bit_test(_usbh_data->attach_debouncing_bm, event->rhport)) {
                    return;
                }

                if (event->event_id == HCD_EVENT_DEVICE_ATTACH) {
                    _usbh_data->attach_debouncing_bm |= TU_BIT(event->rhport);
                }
            }
            break;
        }
        default: {
            break;
        }
    }

    if (!event_enqueue(&event_qh, *event)) {
        sddf_notify(USB_PROTOCOL_STACK);
    } else {
        /* TODO: Handle this */
        sddf_dprintf("USB DRIVER|ERROR: The event queue is full\n");
    }
}

TU_ATTR_ALWAYS_INLINE static inline usbh_device_t *get_device(uint8_t dev_addr) {
    TU_VERIFY(dev_addr > 0 && dev_addr <= TOTAL_DEVICES, NULL);
    return &_usbh_devices[dev_addr - 1];
}

bool tuh_bus_info_get(uint8_t daddr, tuh_bus_info_t *bus_info) {
    usbh_device_t const* dev = get_device(daddr);

    if (dev != NULL) {
        *bus_info = dev->bus_info;
    } else {
        *bus_info = _usbh_data->dev0_bus;
    }

    return true;
}
