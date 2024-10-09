// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright 2017-2018 NXP.
 *
 * Derived from: https://github.com/torvalds/linux/blob/75b607fab38d149f232f01eae5e6392b394dd659/drivers/clk/imx/clk-imx8mm.c
 */

#include <clk-provider.h>
#include <clk.h>
#include <imx8mm.h>
#include <clk-imx8mm.h>
#include <sddf/util/util.h>
#include <clk-operations.h>

#define MASK(width)  ((1UL << width) - 1)

static CLK_HW_SOURCE(dummy, 0);
static CLK_HW_SOURCE(osc_24m, 24000000);

static struct clk_parent_data pll_ref_sels[] = {
    { .clk = &osc_24m, },
    { .clk = &dummy, },
    { .clk = &dummy, },
    { .clk = &dummy, },
};

static CLK_HW_MUX(audio_pll1_ref_sel, 0x0, MASK(2), 0, 0, 0, pll_ref_sels, ARRAY_SIZE(pll_ref_sels), 0);

static struct clk *imx8mm_clks[] = {
    [IMX8MM_AUDIO_PLL1_REF_SEL]     = &audio_pll1_ref_sel,
};

struct clk **get_clk_list(void)
{
    return imx8mm_clks;
}
