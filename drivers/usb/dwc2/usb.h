/*
 * The MIT License (MIT)
 *
 * Copyright (c) 2019 Ha Thach (tinyusb.org)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#pragma once

#include <tusb.h>

/* Types common to the the protocol stack and the driver */

#ifndef CFG_TUH_INTERFACE_MAX
  #define CFG_TUH_INTERFACE_MAX   8
#endif

// sum of end device + hub
#define TOTAL_DEVICES   (CFG_TUH_DEVICE_MAX + CFG_TUH_HUB)

typedef void (*tusb_defer_func_t)(uintptr_t param);

//--------------------------------------------------------------------+
// Data Structure
//--------------------------------------------------------------------+

// Device Descriptor (without bLength and bDescriptorType header)
typedef struct TU_ATTR_PACKED {
  uint16_t bcdUSB;
  uint8_t  bDeviceClass;
  uint8_t  bDeviceSubClass;
  uint8_t  bDeviceProtocol;
  uint8_t  bMaxPacketSize0;
  uint16_t idVendor;
  uint16_t idProduct;
  uint16_t bcdDevice;
  uint8_t  iManufacturer;
  uint8_t  iProduct;
  uint8_t  iSerialNumber;
  uint8_t  bNumConfigurations;
} desc_device_noheader_t;

TU_VERIFY_STATIC( sizeof(desc_device_noheader_t) == 16u, "size is not correct");

typedef struct {
  tuh_bus_info_t bus_info;
  desc_device_noheader_t desc_device;

  // Device State
  struct TU_ATTR_PACKED {
    volatile uint8_t connected  : 1; // After 1st transfer
    volatile uint8_t addressed  : 1; // After SET_ADDR
    volatile uint8_t configured : 1; // After SET_CONFIG and all drivers are configured
    volatile uint8_t suspended  : 1; // Bus suspended
    // volatile uint8_t removing : 1; // Physically disconnected, waiting to be processed by usbh
  };

  // Endpoint & Interface
  uint8_t itf2drv[CFG_TUH_INTERFACE_MAX];  // map interface number to driver (0xff is invalid)
  uint8_t ep2drv[CFG_TUH_ENDPOINT_MAX][2]; // map endpoint to driver ( 0xff is invalid ), can use only 4-bit each

  volatile uint8_t ep_status[CFG_TUH_ENDPOINT_MAX][2];

#if CFG_TUH_API_EDPT_XFER
  // TODO array can be CFG_TUH_ENDPOINT_MAX-1
  struct {
    tuh_xfer_cb_t complete_cb;
    uintptr_t user_data;
  }ep_callback[CFG_TUH_ENDPOINT_MAX][2];
#endif

} usbh_device_t;

// Control transfers: since most controllers do not support multiple control transfers
// on multiple devices concurrently and control transfers are not used much except for
// enumeration, we will only execute control transfers one at a time.
typedef struct {
  uint8_t* buffer;
  tuh_xfer_cb_t complete_cb;
  uintptr_t user_data;

  volatile uint16_t actual_len;
  volatile uint8_t stage;
  uint8_t daddr;
  uint8_t failed_count;
} usbh_ctrl_xfer_info_t;

typedef struct {
  tusb_defer_func_t func;
  uintptr_t         arg;
  uint32_t          at_ms;
} usbh_call_after_t;

typedef struct {
  tusb_control_request_t setup;
  uint8_t*               buffer;
  tuh_xfer_cb_t          complete_cb;
  uintptr_t              user_data;
  uint8_t                daddr;
  uint8_t                daddr_gen;
} usbh_pending_ctrl_t;

// sum of end device + hub
#define TOTAL_DEVICES   (CFG_TUH_DEVICE_MAX + CFG_TUH_HUB)

typedef struct {
  uint8_t enumerating_daddr;  // device address of the device being enumerated
  uint8_t attach_debouncing_bm;  // bitmask for roothub port attach debouncing
  tuh_bus_info_t dev0_bus;    // bus info for dev0 in enumeration
  usbh_ctrl_xfer_info_t ctrl_xfer_info; // control transfer
  usbh_call_after_t call_after;
  // Per-daddr generation counter — bumped on usbh_device_close() to identify stale pending control transfer
  uint8_t daddr_gen[TOTAL_DEVICES + 1];
#if CFG_TUSB_OS_HAS_SCHEDULER
  osal_task_handle_t task_hdl;  // host task handle, lazy-captured on first tuh_task_ext()
#endif
} usbh_data_t;
