#include <sddf/util/printf.h>
#include <os/sddf.h>

#include <sddf/timer/client.h>
#include <sddf/timer/config.h>

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


void tuh_hid_report_received_cb(uint8_t dev_addr, uint8_t instance, uint8_t const *report, uint16_t len) {
    LOG_USB("recieved HID report\n");
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
        LOG_USB("init tinyUSB stack...\n");

        LOG_USB("Initialising TinyUSB...\n");
        tusb_rhport_init_t host_init = {
            .role = TUSB_ROLE_HOST,
            .speed = TUSB_SPEED_AUTO
        };

        // TODO: rhport is for companion controller, which I have not configured (yet?)
        uint8_t caplength = *(uint8_t*)(ehci_regs + 0);

        ehci_init(0, ehci_regs, ehci_regs + caplength);
        
        tusb_init(BOARD_TUH_RHPORT, &host_init);

        LOG_USB("init complete\n");
    }

    else if (ch == usb_irq_channel) {
        LOG_USB("recieved interrupt!\n");
        /* copied verbatim from alexd */

    }
}

