/*
 * The USB host example source code was obtained from TinyUSB's examples; it is
 * licensed under the MIT License and is Copyright (c) 2019-2025, hatach
 * (tinyusb.org).
 * 
 * All other source code has a BSD 2-Clause License and is Copyright 2025, UNSW.
 * 
 * SPDX-License-Identifier: BSD-2-Clause AND MIT
 */

#include <inttypes.h>
#include <stdint.h>
#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <sddf/util/cache.h>
#include <sddf/util/printf.h>

#include <tusb.h>
#include <common/tusb_debug.h>

#include <broadcom/cpu.h>
#include <broadcom/defines.h>
#include <broadcom/gen/vcmailbox.h>


#define LOG_USB(...) do{ sddf_dprintf("USB|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

sddf_channel timer_channel;

sddf_channel microkit_usb_irq;

void hid_app_task(void);
bool vcmailbox_set_power_state(vcmailbox_device_t device, bool on);

void board_init(void)
{
    vcmailbox_set_power_state(VCMAILBOX_DEVICE_USB_HCD, true);
}

int board_uart_write(void const *buf, int len)
{
    microkit_dbg_puts((const char *) buf);
    return len;
}

int board_uart_read(uint8_t *buf, int len)
{
    return 0;
}

uint32_t board_millis(void)
{
    return sddf_timer_time_now(timer_channel) / NS_IN_MS;
}

void tuh_event_hook_cb(uint8_t rhport, uint32_t eventid, bool in_isr)
{
    // LOG_USB("An event is ready to be processed\n");
}

// To ensure we loaded the correct data, we must have the CPU wait for pending
// reads before moving onto reads from other peripherals. This is done with a
// memory barrier instruction.
#if defined(__ARM_ARCH) && (__ARM_ARCH >= 8)
#define COMPLETE_MEMORY_READS __asm__ volatile ("dsb sy")
#define STRICT_ALIGN __attribute__((target("strict-align")))
#else
#define COMPLETE_MEMORY_READS __asm__ volatile ("mcr p15, 0, %[zero], c7, c10, 5" : : [zero] "r" (0) : "memory")
#define STRICT_ALIGN
#endif

// Writes values from the cache back into memory but keep a copy in the cache.
STRICT_ALIGN void data_clean(volatile void* starting_address, size_t size) {
    unsigned long start = (unsigned long) starting_address;
    unsigned long end = (unsigned long) starting_address + size;
    cache_clean(start, end);
}

// Writes values from the cache back into memory and remove it from the cache.
STRICT_ALIGN void data_clean_and_invalidate(volatile void* starting_address, size_t size) {
    unsigned long start = (unsigned long) starting_address;
    unsigned long end = (unsigned long) starting_address + size;
    cache_clean_and_invalidate(start, end);
}

// Remove values from the cache because the value in memory may have changed.
STRICT_ALIGN void data_invalidate(volatile void* starting_address, size_t size) {
    unsigned long start = (unsigned long) starting_address;
    unsigned long end = (unsigned long) starting_address + size;
    cache_clean_and_invalidate(start, end);
}

STRICT_ALIGN bool vcmailbox_request(volatile vcmailbox_buffer_t* buffer) {
    size_t buffer_size = buffer->buffer_size;
    buffer->code = VCMAILBOX_CODE_PROCESS_REQUEST;
    COMPLETE_MEMORY_READS;
    while (VCMAILBOX->STATUS0_b.FULL) {}
    while (!VCMAILBOX->STATUS0_b.EMPTY) {
        VCMAILBOX->READ;
    }
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wpointer-to-int-cast"
    uint32_t buffer_address = 0x00000000 | (uint32_t) buffer | 8;
    #pragma GCC diagnostic pop
    data_clean(buffer, buffer_size);
    
    VCMAILBOX->WRITE = buffer_address;
    size_t count = 0;
    while (VCMAILBOX->STATUS0_b.EMPTY || VCMAILBOX->READ != buffer_address) {
        count++;
        if (count > 10000000) {
            return false;
        }
    }
    COMPLETE_MEMORY_READS;
    data_invalidate(buffer, buffer_size);
    return buffer->code == VCMAILBOX_CODE_REQUEST_SUCCESSFUL;
}

STRICT_ALIGN uint32_t compute_size(uint32_t tag_size) {
    uint32_t size = VCMAILBOX_HEADER_SIZE + tag_size + sizeof(uint32_t);
    if (size % 16 != 0) {
        size += 16 - (size % 16);
    }
    return size;
}

bool vcmailbox_set_power_state(vcmailbox_device_t device, bool on) {
    int size = compute_size(sizeof(vcmailbox_set_power_state_t));
    vcmailbox_buffer_t* buf = (vcmailbox_buffer_t*) __builtin_alloca_with_align(size, 16 * 8);
    memset(buf, 0, size);
    buf->buffer_size = size;
    vcmailbox_set_power_state_t* tag = (vcmailbox_set_power_state_t*) &buf->data;
    tag->tag = VCMAILBOX_TAG_SET_POWER_STATE;
    tag->is_response = false;
    tag->request.device_id = (uint32_t) device;
    tag->value_size = sizeof(vcmailbox_set_power_state_request_t);
    // Always wait for power stability.
    tag->request.state = on ? 0x3 : 0x2;
    vcmailbox_request(buf);
    return tag->response.state == 1;
}

void notified(sddf_channel ch)
{
  if (ch == 0) {
    /* Temporary: ISR should be in its own protection domain with higher
     * priority than the domain that calls tuh_task() */
    tusb_int_handler(0, true);
    sddf_irq_ack(ch);
    tuh_task();
    hid_app_task();
  }
}

void init(void)
{
    LOG_USB("Starting...\n");
    assert(timer_config_check_magic(&config));
    timer_channel = config.driver_id;
    microkit_usb_irq = 0;
    uint64_t time = sddf_timer_time_now(timer_channel);
    LOG_USB("Time is: %lu\n", time);

    LOG_USB("Initialising the board...\n");
    board_init();

    LOG_USB("Initialising TinyUSB...\n");
    tusb_rhport_init_t host_init = {
        .role = TUSB_ROLE_HOST,
        .speed = TUSB_SPEED_AUTO
    };
    tusb_init(BOARD_TUH_RHPORT, &host_init);

    LOG_USB("Initialisation finished!\n");
    TU_LOG1("Debug level 1 enabled\n");
    TU_LOG2("Debug level 2 enabled\n");
    TU_LOG3("Debug level 3 enabled\n");
}

/* TinyUSB example */

void tuh_mount_cb(uint8_t dev_addr) {
  // application set-up
  LOG_USB("A device with address %u is mounted\n", dev_addr);
}

void tuh_umount_cb(uint8_t dev_addr) {
  // application tear-down
  LOG_USB("A device with address %u is unmounted\n", dev_addr);
}

/* TinyUSB MSC example */

static scsi_inquiry_resp_t inquiry_resp;

bool msc_data_written_cb(uint8_t dev_addr, const tuh_msc_complete_data_t *cb_data)
{
  LOG_USB("Apparentely we finished writing to the disk\n");
  return true;
}

static bool inquiry_complete_cb(uint8_t dev_addr, tuh_msc_complete_data_t const * cb_data) {
  msc_cbw_t const* cbw = cb_data->cbw;
  msc_csw_t const* csw = cb_data->csw;

  if (csw->status != 0) {
    LOG_USB("Inquiry failed\n");
    return false;
  }

  // Print out Vendor ID, Product ID and Rev
  LOG_USB("%.8s %.16s rev %.4s\n", inquiry_resp.vendor_id, inquiry_resp.product_id, inquiry_resp.product_rev);

  // Get capacity of device
  uint32_t const block_count = tuh_msc_get_block_count(dev_addr, cbw->lun);
  uint32_t const block_size = tuh_msc_get_block_size(dev_addr, cbw->lun);

  LOG_USB("Disk Size: %u MB\n", block_count / ((1024*1024)/block_size));
  LOG_USB("Block Count = %u, Block Size: %u\n", block_count, block_size);

//   // Block write test
//   char hello[512] = "Hello world!";
//   if (tuh_msc_write10(dev_addr, 0, hello, 10000, 1, msc_data_written_cb, 0)) {
//       LOG_USB("Write queued\n");
//   } else {
//       LOG_USB("Write was not queued\n");
//   }

  return true;
}

//------------- IMPLEMENTATION -------------//

bool msc_sync_cb(uint8_t dev_addr, const tuh_msc_complete_data_t *cb_data)
{
  LOG_USB("Apparentely we synced\n");
  return true;
}

void tuh_msc_mount_cb(uint8_t dev_addr) {
  LOG_USB("A MassStorage device is mounted\n");

  uint8_t const lun = 0;
  tuh_msc_inquiry(dev_addr, lun, &inquiry_resp, inquiry_complete_cb, 0);

  // msc_cbw_t cbw;
  // tu_memclr(&cbw, sizeof(msc_cbw_t));
  // cbw.signature = MSC_CBW_SIGNATURE;
  // cbw.tag       = 0x54555342; // TUSB
  // cbw.lun       = lun;
  // cbw.dir       = 0; // change
  // cbw.lun       = lun;
  // cbw.tag       = -0; // ?
  // cbw.total_bytes = 512;

  // msc_cbw_t cbw = {
  //   .cmd_len = 0,
  //   .command = 0,
  //   .dir = 0,
  //   .tag = 0,
  // };

  // if (!tuh_msc_scsi_command(dev_addr, &cbw, NULL, msc_sync_cb, 0)) {
  //   LOG_USB("Operation already pending\n");
  // }
}

void tuh_msc_umount_cb(uint8_t dev_addr) {
  (void) dev_addr;
  LOG_USB("A MassStorage device is unmounted\n");
}

/* TinyUSB HID example */

//--------------------------------------------------------------------+
// MACRO TYPEDEF CONSTANT ENUM DECLARATION
//--------------------------------------------------------------------+
#define MAX_REPORT 4

static uint8_t const keycode2ascii[128][2] = {HID_KEYCODE_TO_ASCII};

// Each HID instance can has multiple reports
static struct {
  uint8_t report_count;
  tuh_hid_report_info_t report_info[MAX_REPORT];
} hid_info[CFG_TUH_HID];

static void process_kbd_report(hid_keyboard_report_t const *report);
static void process_mouse_report(hid_mouse_report_t const *report);
static void process_generic_report(uint8_t dev_addr, uint8_t instance, uint8_t const *report, uint16_t len);

void hid_app_task(void) {
  // nothing to do
}

//--------------------------------------------------------------------+
// TinyUSB Callbacks
//--------------------------------------------------------------------+

// Invoked when device with hid interface is mounted
// Report descriptor is also available for use. tuh_hid_parse_report_descriptor()
// can be used to parse common/simple enough descriptor.
// Note: if report descriptor length > CFG_TUH_ENUMERATION_BUFSIZE, it will be skipped
// therefore report_desc = NULL, desc_len = 0
void tuh_hid_mount_cb(uint8_t dev_addr, uint8_t instance, uint8_t const *desc_report, uint16_t desc_len) {
  LOG_USB("HID device address = %d, instance = %d is mounted\n", dev_addr, instance);

  // Interface protocol (hid_interface_protocol_enum_t)
  const char *protocol_str[] = {"None", "Keyboard", "Mouse"};
  uint8_t const itf_protocol = tuh_hid_interface_protocol(dev_addr, instance);

  LOG_USB("HID Interface Protocol = %s\n", protocol_str[itf_protocol]);

  // By default, host stack will use boot protocol on supported interface.
  // Therefore for this simple example, we only need to parse generic report descriptor (with built-in parser)
  if (itf_protocol == HID_ITF_PROTOCOL_NONE) {
    hid_info[instance].report_count = tuh_hid_parse_report_descriptor(hid_info[instance].report_info, MAX_REPORT, desc_report, desc_len);
    LOG_USB("HID has %u reports \n", hid_info[instance].report_count);
  }

  // request to receive report
  // tuh_hid_report_received_cb() will be invoked when report is available
  if (!tuh_hid_receive_report(dev_addr, instance)) {
    LOG_USB("Error: cannot request to receive report\n");
  }
}

// Invoked when device with hid interface is un-mounted
void tuh_hid_umount_cb(uint8_t dev_addr, uint8_t instance) {
  LOG_USB("HID device address = %d, instance = %d is unmounted\n", dev_addr, instance);
}

// Invoked when received report from device via interrupt endpoint
void tuh_hid_report_received_cb(uint8_t dev_addr, uint8_t instance, uint8_t const *report, uint16_t len) {
  uint8_t const itf_protocol = tuh_hid_interface_protocol(dev_addr, instance);

  switch (itf_protocol) {
    case HID_ITF_PROTOCOL_KEYBOARD:
      TU_LOG2("HID receive boot keyboard report\n");
      process_kbd_report((hid_keyboard_report_t const *) report);
      break;

    case HID_ITF_PROTOCOL_MOUSE:
      TU_LOG2("HID receive boot mouse report\n");
      process_mouse_report((hid_mouse_report_t const *) report);
      break;

    default:
      // Generic report requires matching ReportID and contents with previous parsed report info
      process_generic_report(dev_addr, instance, report, len);
      break;
  }

  // continue to request to receive report
  if (!tuh_hid_receive_report(dev_addr, instance)) {
    LOG_USB("Error: cannot request to receive report\n");
  }
}

//--------------------------------------------------------------------+
// Keyboard
//--------------------------------------------------------------------+

// look up new key in previous keys
static inline bool find_key_in_report(hid_keyboard_report_t const *report, uint8_t keycode) {
  for (uint8_t i = 0; i < 6; i++) {
    if (report->keycode[i] == keycode) {
      return true;
    }
  }
  return false;
}

static void process_kbd_report(hid_keyboard_report_t const *report) {
  static hid_keyboard_report_t prev_report = {0, 0, {0}};// previous report to check key released

  //------------- example code ignore control (non-printable) key affects -------------//
  for (uint8_t i = 0; i < 6; i++) {
    if (report->keycode[i]) {
      if (find_key_in_report(&prev_report, report->keycode[i])) {
        // exist in previous report means the current key is holding
      } else {
        // not existed in previous report means the current key is pressed
        bool const is_shift = report->modifier & (KEYBOARD_MODIFIER_LEFTSHIFT | KEYBOARD_MODIFIER_RIGHTSHIFT);
        uint8_t ch = keycode2ascii[report->keycode[i]][is_shift ? 1 : 0];
        // putchar(ch);
        // microkit_dbg_putc(ch);
        LOG_USB("%c\n", ch);
        // sddf_dprintf("%c\n", ch);
        
        if (ch == '\0') {
          // LOG_USB("%c", '\n');
        // microkit_dbg_puts("\n");
          // sddf_dprintf(" \n");
        LOG_USB(" \n");

          // sddf_dprintf("\n");
        //   putchar('\n');
        }

        // #ifndef __ICCARM__     // TODO IAR doesn't support stream control ?
        // fflush(stdout);// flush right away, else nanolib will wait for newline
        // #endif
      }
    }
    // TODO example skips key released
  }

  prev_report = *report;
}

//--------------------------------------------------------------------+
// Mouse
//--------------------------------------------------------------------+

static void cursor_movement(int8_t x, int8_t y, int8_t wheel) {
  LOG_USB("(%d %d %d)\n", x, y, wheel);
}

static void process_mouse_report(hid_mouse_report_t const *report) {
  static hid_mouse_report_t prev_report = {0};

  // button state
  uint8_t button_changed_mask = report->buttons ^ prev_report.buttons;
  if (button_changed_mask & report->buttons) {
    LOG_USB(" %c%c%c \n",
           report->buttons & MOUSE_BUTTON_LEFT ? 'L' : '-',
           report->buttons & MOUSE_BUTTON_MIDDLE ? 'M' : '-',
           report->buttons & MOUSE_BUTTON_RIGHT ? 'R' : '-');
  }

  // cursor movement
  cursor_movement(report->x, report->y, report->wheel);
}

//--------------------------------------------------------------------+
// Generic Report
//--------------------------------------------------------------------+
static void process_generic_report(uint8_t dev_addr, uint8_t instance, uint8_t const *report, uint16_t len) {
  (void) dev_addr;
  (void) len;

  uint8_t const rpt_count = hid_info[instance].report_count;
  tuh_hid_report_info_t *rpt_info_arr = hid_info[instance].report_info;
  tuh_hid_report_info_t *rpt_info = NULL;

  if (rpt_count == 1 && rpt_info_arr[0].report_id == 0) {
    // Simple report without report ID as 1st byte
    rpt_info = &rpt_info_arr[0];
  } else {
    // Composite report, 1st byte is report ID, data starts from 2nd byte
    uint8_t const rpt_id = report[0];

    // Find report id in the array
    for (uint8_t i = 0; i < rpt_count; i++) {
      if (rpt_id == rpt_info_arr[i].report_id) {
        rpt_info = &rpt_info_arr[i];
        break;
      }
    }

    report++;
    len--;
  }

  if (!rpt_info) {
    LOG_USB("Couldn't find report info !\n");
    return;
  }

  // For complete list of Usage Page & Usage checkout src/class/hid/hid.h. For examples:
  // - Keyboard                     : Desktop, Keyboard
  // - Mouse                        : Desktop, Mouse
  // - Gamepad                      : Desktop, Gamepad
  // - Consumer Control (Media Key) : Consumer, Consumer Control
  // - System Control (Power key)   : Desktop, System Control
  // - Generic (vendor)             : 0xFFxx, xx
  if (rpt_info->usage_page == HID_USAGE_PAGE_DESKTOP) {
    switch (rpt_info->usage) {
      case HID_USAGE_DESKTOP_KEYBOARD:
        TU_LOG2("HID receive keyboard report\n");
        // Assume keyboard follow boot report layout
        process_kbd_report((hid_keyboard_report_t const *) report);
        break;

      case HID_USAGE_DESKTOP_MOUSE:
        TU_LOG2("HID receive mouse report\n");
        // Assume mouse follow boot report layout
        process_mouse_report((hid_mouse_report_t const *) report);
        break;

      default:
        LOG_USB("report[%u] ", rpt_info->report_id);
        for (uint8_t i = 0; i < len; i++) {
          LOG_USB("%02X ", report[i]);
        }
        LOG_USB("\n");
        break;
    }
  }
}
