#include <sddf/util/printf.h>
#include <os/sddf.h>

#include <sddf/timer/client.h>
#include <sddf/timer/config.h>


#define LOG_USB(...) do{ sddf_dprintf("USB|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)

__attribute__((__section__(".timer_client_config"))) timer_client_config_t config;

// hack: right now, keep in sync with pcie.c (which tells the controller to use the physical addr
// which is mapped to this vaddr by microkit)
uintptr_t ehci_regs = 0x30000000;

// hack: also keep up to date with pcie.c
sddf_channel pcie_channel = 3;
sddf_channel usb_irq_channel = 1;
sddf_channel timer_channel;

void init(void)
{
    LOG_USB("init...\n");

    assert(timer_config_check_magic(&config));
    timer_channel = config.driver_id;

    LOG_USB("timer on channel %d\n", timer_channel);

    assert(pcie_channel != usb_irq_channel);
    assert(pcie_channel != timer_channel);

    LOG_USB("calling into timer driver...\n");
    uint64_t time = sddf_timer_time_now(timer_channel);
    LOG_USB("Time is: %lu\n", time);

    LOG_USB("init complete\n");

}


void print_ehci(void) {
    LOG_USB("caplength=0x%x\n", *(uint8_t*)(ehci_regs + 0));
    LOG_USB("ver=0x%x\n", *(uint16_t*)(ehci_regs + 2));
    LOG_USB("sparams=0x%x\n", *(uint32_t*)(ehci_regs + 4));
    LOG_USB("cparams=0x%x\n", *(uint32_t*)(ehci_regs + 8));
    LOG_USB("port route desc=0x%x\n", *(uint32_t*)(ehci_regs + 12));
}

void notified(sddf_channel ch)
{
    if (ch == pcie_channel) {
        LOG_USB("ehci init complete!\n");

        print_ehci();
    }

    else if (ch == usb_irq_channel) {
        LOG_USB("recieved interrupt!\n");
    }
}

