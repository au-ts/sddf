#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <clk_config.h>

uintptr_t clk_regs;
uintptr_t msr_clk_base;

void notified(microkit_channel ch)
{

}

void init(void)
{
    sddf_dprintf("clk_regs: 0x%lx\n", clk_regs);

    for (int i = 0; i < NUM_DEVICE_CLKS; i++) {
        uint32_t idx = clk_configs[i].clk_id;
        uint32_t rate = clk_configs[i].frequency;

        sddf_dprintf("idx: %u, frequency: 0x%x\n", idx, rate);
    }
}
