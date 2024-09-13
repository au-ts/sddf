#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <clk_config.h>

uintptr_t clk_regs;

void notified(microkit_channel ch)
{

}

void init(void)
{
    sddf_dprintf("clk_regs: 0x%x\n", clk_regs);
}
