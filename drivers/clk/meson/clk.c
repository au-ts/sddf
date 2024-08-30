/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */


#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>

/* Test for Odroid-C4 */
#include <clk.h>

#define I2C_CLK_OFFSET 320
#define I2C_CLK81_BIT (1 << 9) // bit 9

uintptr_t clk_regs;

void notified(microkit_channel ch)
{

}

void init(void)
{
    volatile uint32_t *clk81_ptr        = ((void *)clk_regs + I2C_CLK_OFFSET);

    sddf_dprintf("Clock driver initialising...\n");
    sddf_dprintf("CLKID_I2C: %u\n", CLKID_I2C);
    clk_enable(clk_regs, sm1_clks[CLKID_I2C]);

    // Check that registers actually changed
    if (!(*clk81_ptr & I2C_CLK81_BIT)) {
        sddf_dprintf("failed to toggle clock!\n");
    }
}
