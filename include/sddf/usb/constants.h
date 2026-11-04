/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/* Sizes */
#define CHAR_BIT        8
#define NUM_KEYCODES    6

/* Message registers labels */
#define RET_VAL         0
#define RHPORT          0
#define FRAME_NUMBER    0
#define PORT_SPEED      0

#define IN_ISR          1
#define CFG_ID          1
#define DEV_ADDR        1
#define DEST            1
#define RH_INIT         1
#define RH_ROLE         1

#define CFG_PARAM       2
#define EP_DESC         2
#define EP_ADDR         2
#define BUFFER          2
#define SETUP_HI        2
#define RH_SPEED        2
#define EP_DESC_HI      2

#define BUFLEN          3
#define SETUP_LO        3
#define EP_DESC_LO      3

/* Protected procedure call labels */
enum {
    HCD_CONFIGURE           = 0,
    HCD_INIT                = 1,
    HCD_INT_HANDLER         = 2,
    HCD_INT_ENABLE          = 3,
    HCD_INT_DISABLE         = 4,
    HCD_FRAME_NUMBER        = 5,

    HCD_PORT_CONNECT_STATUS = 11,
    HCD_PORT_RESET          = 12,
    HCD_PORT_RESET_END      = 13,
    HCD_PORT_SPEED_GET      = 14,
    HCD_DEVICE_CLOSE        = 15,

    HCD_EDPT_OPEN           = 20,
    HCD_EDPT_CLOSE          = 21,
    HCD_EDPT_XFER           = 22,
    HCD_EDPT_ABORT_XFER     = 23,
    HCD_SETUP_SEND          = 24,
    HCD_EDPT_CLEAR_STALL    = 25
};

/* Procedure outcomes */
#define FAILURE 0
#define SUCCESS 1

/* USB shared mappings */
#define _USBH_DEVICES_VADDR             0x70000000  /* 2048 B */
#define _HCD_DATA_VADDR                 0x70000800  /* 1024 B */
#define _USBH_EPBUF_VADDR               0x70000C00  /*  512 B */
#define _USBH_DATA_VADDR                0x70000E00  /*  256 B */
#define HUB_EPBUFS_VADDR                0x70000F00  /*  256 B */
#define _MSCH_EPBUF_VADDR               0x70001000  /* 4096 B */
#define _HIDH_EPBUF_VADDR               0x70002000  /* 8096 B */

/* Prototype device information pages */
#define MSC_DEVICE_VADDR                0x70004000
#define HID_DEVICE_VADDR                0x70004100

/* Prototype queue configuration */
#define EVENT_QUEUE_CAPACITY            128
#define EVENT_QUEUE_VADDR               0x71000000
#define EVENT_DATA_VADDR                0x72000000

#define VIRT_REPORT_QUEUE_CAPACITY      256
#define VIRT_REPORT_QUEUE_VADDR         0x71001000
#define VIRT_REPORT_DATA_VADDR          0x72001000

#define CLIENT_REPORT_QUEUE_CAPACITY    256
#define CLIENT_REPORT_QUEUE_VADDR       0x71002000
#define CLIENT_REPORT_DATA_VADDR        0x72002000

#define CLIENT_ASCII_QUEUE_CAPACITY     4096
#define CLIENT_ASCII_QUEUE_VADDR        0x71003000
#define CLIENT_ASCII_DATA_VADDR         0x72003000

/* Prototype channels */

/* According to the driver... */
#define USB_PROTOCOL_STACK              1

/* According to the protocol stack... */
#define USB_DRIVER                      0

/* Protocol stack--HID virtualiser */
#define USB_PROTOCOL_REQUEST_REPORT     15
#define HID_VIRT_REPORT_REQUEST         15
#define HID_VIRT_MOUNT                  31
#define HID_VIRT_UNMOUNT                32
#define HID_VIRT_REPORT_AVAILABLE       33

/* HID virtualiser--client */
#define CLIENT_HID_MOUNT                41
#define CLIENT_HID_UNMOUNT              42
#define CLIENT_HID_ASCII_AVAILABLE      43
#define CLIENT_HID_REPORT_AVAILABLE     44

/* Protocol stack--MSC virtualiser */
#define VIRT_MSC_MOUNT                  20
#define VIRT_MSC_UNMOUNT                21
#define MSC_VIRT_INQUIRY                23

/* MSC virtualiser--client */
#define CLIENT_MSC_INQUIRY              0
#define CLIENT_MSC_PPC                  30
#define CLIENT_MSC_MOUNT                31
#define CLIENT_MSC_UNMOUNT              32
