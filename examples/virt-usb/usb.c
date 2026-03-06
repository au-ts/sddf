#include <sddf/util/printf.h>
#include <os/sddf.h>

#include <sddf/timer/client.h>
#include <sddf/timer/config.h>

#include <sddf/util/cache.h>


#include <tusb.h>
#include <common/tusb_debug.h>

#include <ehci.h>
#include <ehci_api.h>



#define CFG_TUH_ENABLED 1
#define TUP_USBIP_EHCI 1

#define LOG_USB(...) do{ sddf_dprintf("USB|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

// hack: right now, keep in sync with pcie.c (which tells the controller to use the physical addr
// which is mapped to this vaddr by microkit)

// this is also hardcoded in hcd_ehci_virt.c
uintptr_t ehci_regs = 0x30000000;

// hack: also keep up to date with pcie.c
sddf_channel pcie_channel = 3;
sddf_channel usb_irq_channel = 1;
sddf_channel timer_channel;

/* TODO: this prob shouldnt be here */
uint32_t board_millis(void)
{
    return sddf_timer_time_now(timer_channel) / NS_IN_MS;
}



void init(void)
{
    LOG_USB("init...\n");

    assert(timer_config_check_magic(&config));
    timer_channel = config.driver_id;


    assert(pcie_channel != usb_irq_channel);
    assert(pcie_channel != timer_channel);

    uint64_t time = sddf_timer_time_now(timer_channel);
    LOG_USB("Time is: %lu\n", time);

    // set timeout to call tuh task every 1s
    sddf_timer_set_timeout(timer_channel, NS_IN_S);
}


void print_ehci(void) {
    LOG_USB("dumping EHCI cap registers...\n");
    LOG_USB("caplength=0x%x\n", *(uint8_t*)(ehci_regs + 0));
    LOG_USB("ver=0x%x\n", *(uint16_t*)(ehci_regs + 2));
    LOG_USB("sparams=0x%x\n", *(uint32_t*)(ehci_regs + 4));
    LOG_USB("cparams=0x%x\n", *(uint32_t*)(ehci_regs + 8));
    LOG_USB("port route desc=0x%x\n", *(uint32_t*)(ehci_regs + 12));
}

void notified(sddf_channel ch)
{
    if (ch == pcie_channel) {
        LOG_USB("pcie says hello: ehci init complete!\n");

        print_ehci();

        LOG_USB("Initialising TinyUSB...\n");
        tusb_rhport_init_t host_init = {
            .role = TUSB_ROLE_HOST,
            .speed = TUSB_SPEED_AUTO
        };

        // TODO: rhport is for companion controller, which I have not configured (yet?)
        // uint8_t caplength = *(uint8_t*)(ehci_regs + 0);

        // ehci_init(0, ehci_regs, ehci_regs + caplength);
        
        tusb_init(BOARD_TUH_RHPORT, &host_init);

        LOG_USB("init complete\n");
    }

    else if (ch == usb_irq_channel) {
        // LOG_USB("recieved interrupt!\n");
        /* copied verbatim from alexd */
        tusb_int_handler(0, true);
        tuh_task();
        sddf_irq_ack(ch);
    }

    else if (ch == timer_channel) {
        // not needed
        // LOG_USB("received timeout\n");

        // tuh_task();

        // sddf_timer_set_timeout(timer_channel, NS_IN_S);
    }
}

void tuh_msc_mount_cb(uint8_t dev_addr) {
  LOG_USB("A MassStorage device is mounted\n");
}

#define MAX_REPORT 4

static struct {
  uint8_t report_count;
  tuh_hid_report_info_t report_info[MAX_REPORT];
} hid_info[CFG_TUH_HID];

// Invoked when device with hid interface is mounted
// Report descriptor is also available for use. tuh_hid_parse_report_descriptor()
// can be used to parse common/simple enough descriptor.
// Note: if report descriptor length > CFG_TUH_ENUMERATION_BUFSIZE, it will be skipped
// therefore report_desc = NULL, desc_len = 0
void tuh_hid_mount_cb(uint8_t dev_addr, uint8_t instance, uint8_t const *desc_report, uint16_t desc_len) {
  LOG_USB("HID device address = %d, instance = %d is mounted\n", dev_addr, instance);

  const char *protocol_str[] = {"None", "Keyboard", "Mouse"};
  uint8_t const itf_protocol = tuh_hid_interface_protocol(dev_addr, instance);

  LOG_USB("HID Interface Protocol = %s\n", protocol_str[itf_protocol]);
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


static inline bool find_key_in_report(hid_keyboard_report_t const *report, uint8_t keycode) {
  for (uint8_t i = 0; i < 6; i++) {
    if (report->keycode[i] == keycode) {
      return true;
    }
  }
  return false;
}


static uint8_t const keycode2ascii[128][2] = {HID_KEYCODE_TO_ASCII};

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


void tuh_hid_report_received_cb(uint8_t dev_addr, uint8_t instance, uint8_t const *report, uint16_t len) {
    LOG_USB("recieved HID report\n");
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