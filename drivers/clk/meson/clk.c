/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/string.h>
#include <sddf/util/printf.h>
#include <clk_config.h>

/* Test for Odroid-C4 */
#include <clk.h>
#include <clk-operations.h>
#include <clk-measure.h>
#include <g12a.h>
#include <g12a-clkc.h>

#define I2C_CLK_OFFSET 320
#define I2C_CLK_BIT (1 << 9) // bit 9

uintptr_t clk_regs;
uintptr_t msr_clk_base;

static struct clk g12a_fixed_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_FIX_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_FIX_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_FIX_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .frac = {
            .reg_off = HHI_FIX_PLL_CNTL1,
            .shift   = 0,
            .width   = 17,
        },
        .l = {
            .reg_off = HHI_FIX_PLL_CNTL0,
            .shift   = 31,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_FIX_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
    },
    .hw.init = &(struct clk_init_data){
        .name = "fixed_pll_dco",
        .ops = &meson_clk_pll_ro_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
    },
};

static struct clk g12a_fixed_pll = {
    .data = &(struct clk_div_data){
        .offset = HHI_FIX_PLL_CNTL0,
        .shift = 16,
        .width = 2,
        .flags = CLK_DIVIDER_POWER_OF_TWO,
    },
    .hw.init = &(struct clk_init_data){
        .name = "fixed_pll",
        .ops = &clk_regmap_divider_ro_ops,
        .parent_clks = (const struct clk *[]) {
            &g12a_fixed_pll_dco
        },
        .num_parents = 1,
    },
};

#define MESON_FIXED_FACTOR(_name, _mult, _div, _parent_clks, _num_parents, _flags)  \
struct clk _name = {                                                                \
    .data = &(struct clk_fixed_factor_data) {                                       \
        .mult = (_mult),                                                            \
        .div = (_div),                                                              \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_fixed_factor_ops,                                               \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_flags),                                                          \
    },                                                                              \
}

#define MESON_GATE(_name, _offset, _bit, _data_flags, _parent_clks,                 \
                        _num_parents, _hw_flags)                                    \
struct clk _name = {                                                                \
    .data = &(struct clk_gate_data) {                                               \
        .offset = (_offset),                                                        \
        .bit_idx = (_bit),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_gate_ops,                                                \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = _num_parents,                                                \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_MUX(_name, _offset, _mask, _shift, _table,                            \
                  _data_flags, _parent_data, _num_parents, _hw_flags)                \
struct clk _name = {                                                                \
    .data = &(struct clk_mux_data) {                                                \
        .offset = (_offset),                                                        \
        .mask = (_mask),                                                            \
        .shift = (_shift),                                                          \
        .table = (_table),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_mux_ops,                                                 \
        .parent_data = (_parent_data),                                              \
        .num_parents = (_num_parents),                                              \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

#define MESON_DIV(_name, _offset, _shift, _width, _data_flags,                      \
                  _parent_clks, _num_parents, _hw_flags)                            \
struct clk _name = {                                                                \
    .data = &(struct clk_div_data) {                                                \
        .offset = (_offset),                                                        \
        .shift = (_shift),                                                          \
        .width = (_width),                                                          \
        .flags = (_data_flags),                                                     \
    },                                                                              \
    .hw.init = &(struct clk_init_data) {                                            \
        .name = #_name,                                                             \
        .ops = &clk_regmap_divider_ops,                                             \
        .parent_clks = (const struct clk *[]) _parent_clks,                         \
        .num_parents = (_num_parents),                                              \
        .flags = (_hw_flags),                                                       \
    },                                                                              \
}

static MESON_FIXED_FACTOR(g12a_mpll_prediv, 1, 2, { &g12a_fixed_pll_dco }, 1, 0);

static const struct reg_sequence g12a_mpll0_init_regs[] = {
    { .reg = HHI_MPLL_CNTL2,    .def = 0x40000033 },
};
static struct clk g12a_mpll0_div = {
    .data = &(struct meson_clk_mpll_data){
        .sdm = {
            .reg_off = HHI_MPLL_CNTL1,
            .shift   = 0,
            .width   = 14,
        },
        .sdm_en = {
            .reg_off = HHI_MPLL_CNTL1,
            .shift   = 30,
            .width     = 1,
        },
        .n2 = {
            .reg_off = HHI_MPLL_CNTL1,
            .shift   = 20,
            .width   = 9,
        },
        .ssen = {
            .reg_off = HHI_MPLL_CNTL1,
            .shift   = 29,
            .width     = 1,
        },
        .init_regs = g12a_mpll0_init_regs,
        .init_count = ARRAY_SIZE(g12a_mpll0_init_regs),
    },
    .hw.init = &(struct clk_init_data){
        .name = "mpll0_div",
        .ops = &meson_clk_mpll_ops,
        .parent_clks = (const struct clk *[]) {
            &g12a_mpll_prediv
        },
        .num_parents = 1,
    },
};
static MESON_GATE(g12a_mpll0, HHI_MPLL_CNTL1, 31, 0, { &g12a_mpll0_div }, 1, CLK_SET_RATE_PARENT);

static const struct reg_sequence g12a_mpll1_init_regs[] = {
    { .reg = HHI_MPLL_CNTL4,    .def = 0x40000033 },
};
static struct clk g12a_mpll1_div = {
    .data = &(struct meson_clk_mpll_data){
        .sdm = {
            .reg_off = HHI_MPLL_CNTL3,
            .shift   = 0,
            .width   = 14,
        },
        .sdm_en = {
            .reg_off = HHI_MPLL_CNTL3,
            .shift   = 30,
            .width     = 1,
        },
        .n2 = {
            .reg_off = HHI_MPLL_CNTL3,
            .shift   = 20,
            .width   = 9,
        },
        .ssen = {
            .reg_off = HHI_MPLL_CNTL3,
            .shift   = 29,
            .width     = 1,
        },
        .init_regs = g12a_mpll1_init_regs,
        .init_count = ARRAY_SIZE(g12a_mpll1_init_regs),
    },
    .hw.init = &(struct clk_init_data){
        .name = "mpll1_div",
        .ops = &meson_clk_mpll_ops,
        .parent_clks = (const struct clk *[]) {
            &g12a_mpll_prediv
        },
        .num_parents = 1,
    },
};
static MESON_GATE(g12a_mpll1, HHI_MPLL_CNTL3, 31, 0, { &g12a_mpll1_div }, 1, CLK_SET_RATE_PARENT);

static const struct reg_sequence g12a_mpll2_init_regs[] = {
    { .reg = HHI_MPLL_CNTL6, .def = 0x40000033 },
};
static struct clk g12a_mpll2_div = {
    .data = &(struct meson_clk_mpll_data){
        .sdm = {
            .reg_off = HHI_MPLL_CNTL5,
            .shift   = 0,
            .width   = 14,
        },
        .sdm_en = {
            .reg_off = HHI_MPLL_CNTL5,
            .shift   = 30,
            .width     = 1,
        },
        .n2 = {
            .reg_off = HHI_MPLL_CNTL5,
            .shift   = 20,
            .width   = 9,
        },
        .ssen = {
            .reg_off = HHI_MPLL_CNTL5,
            .shift   = 29,
            .width     = 1,
        },
        .init_regs = g12a_mpll2_init_regs,
        .init_count = ARRAY_SIZE(g12a_mpll2_init_regs),
    },
    .hw.init = &(struct clk_init_data){
        .name = "mpll2_div",
        .ops = &meson_clk_mpll_ops,
        .parent_clks = (const struct clk *[]) {
            &g12a_mpll_prediv
        },
        .num_parents = 1,
    },
};
static MESON_GATE(g12a_mpll2, HHI_MPLL_CNTL5, 31, 0, { &g12a_mpll2_div }, 1, CLK_SET_RATE_PARENT);

static const struct reg_sequence g12a_mpll3_init_regs[] = {
	{ .reg = HHI_MPLL_CNTL8,	.def = 0x40000033 },
};
static struct clk g12a_mpll3_div = {
	.data = &(struct meson_clk_mpll_data){
		.sdm = {
			.reg_off = HHI_MPLL_CNTL7,
			.shift   = 0,
			.width   = 14,
		},
		.sdm_en = {
			.reg_off = HHI_MPLL_CNTL7,
			.shift   = 30,
			.width	 = 1,
		},
		.n2 = {
			.reg_off = HHI_MPLL_CNTL7,
			.shift   = 20,
			.width   = 9,
		},
		.ssen = {
			.reg_off = HHI_MPLL_CNTL7,
			.shift   = 29,
			.width	 = 1,
		},
		.init_regs = g12a_mpll3_init_regs,
		.init_count = ARRAY_SIZE(g12a_mpll3_init_regs),
	},
	.hw.init = &(struct clk_init_data){
		.name = "mpll3_div",
		.ops = &meson_clk_mpll_ops,
		.parent_clks = (const struct clk *[]) {
			&g12a_mpll_prediv
		},
		.num_parents = 1,
	},
};
static MESON_GATE(g12a_mpll3, HHI_MPLL_CNTL7, 31, 0, { &g12a_mpll3_div }, 1, CLK_SET_RATE_PARENT);

static MESON_FIXED_FACTOR(g12a_fclk_div2_div, 1, 2, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div2, HHI_FIX_PLL_CNTL1, 24, 0, { &g12a_fclk_div2_div }, 1, CLK_IS_CRITICAL);

static MESON_FIXED_FACTOR(g12a_fclk_div3_div, 1, 3, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div3, HHI_FIX_PLL_CNTL1, 20, 0, { &g12a_fclk_div3_div }, 1, CLK_IS_CRITICAL);

static MESON_FIXED_FACTOR(g12a_fclk_div4_div, 1, 4, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div4, HHI_FIX_PLL_CNTL1, 21, 0, { &g12a_fclk_div4_div }, 1, 0);

static MESON_FIXED_FACTOR(g12a_fclk_div5_div, 1, 5, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div5, HHI_FIX_PLL_CNTL1, 22, 0, { &g12a_fclk_div5_div }, 1, 0);

static MESON_FIXED_FACTOR(g12a_fclk_div7_div, 1, 7, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div7, HHI_FIX_PLL_CNTL1, 23, 0, { &g12a_fclk_div5_div }, 1, 0);

static const struct clk_parent_data g12a_hdmi_parent_data[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div4 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &g12a_fclk_div5 },
};
static MESON_MUX(g12a_hdmi_sel, HHI_HDMI_CLK_CNTL, 0x3, 9, NULL, CLK_MUX_ROUND_CLOSEST, g12a_hdmi_parent_data, ARRAY_SIZE(g12a_hdmi_parent_data), CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_DIV(g12a_hdmi_div, HHI_HDMI_CLK_CNTL, 0, 7, 0, { &g12a_hdmi_sel }, 1, CLK_GET_RATE_NOCACHE);
static MESON_GATE(g12a_hdmi, HHI_HDMI_CLK_CNTL, 8, 0, { &g12a_hdmi_div }, 1, CLK_SET_RATE_PARENT | CLK_IGNORE_UNUSED);

static uint32_t mux_table_clk81[]    = { 0, 2, 3, 4, 5, 6, 7 };
static const struct clk_parent_data clk81_parent_data[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div7 },
    { .clk = &g12a_mpll1 },
    { .clk = &g12a_mpll2 },
    { .clk = &g12a_fclk_div4 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &g12a_fclk_div5 },
};

static MESON_MUX(g12a_mpeg_clk_sel, HHI_MPEG_CLK_CNTL, 0x7, 12, mux_table_clk81, 0, clk81_parent_data, ARRAY_SIZE(clk81_parent_data), 0);
static MESON_DIV(g12a_mpeg_clk_div, HHI_MPEG_CLK_CNTL, 0, 7, 0, { &g12a_mpeg_clk_sel }, 1, 0);
static MESON_GATE(g12a_clk81, HHI_MPEG_CLK_CNTL, 7, 0, { &g12a_mpeg_clk_div }, 1, 0);

#define MESON_CLK81_GATE(_name, _reg, _bit)                  \
struct clk _name = {                                         \
    .data = &(struct clk_gate_data) {                        \
        .offset = (_reg),                                    \
        .bit_idx = (_bit),                                   \
        .flags = 0,                                          \
    },                                                       \
    .hw.init = &(struct clk_init_data) {                     \
        .name = #_name,                                      \
        .ops = &clk_regmap_gate_ops,                         \
        .parent_clks = (const struct clk *[]) {              \
            &g12a_clk81,                                     \
        },                                                   \
        .num_parents = 1,                                    \
        .flags = 0,                                          \
    },                                                       \
}

#define MESON_CLK81_GATE_RO(_name, _reg, _bit)               \
struct clk _name = {                                         \
    .data = &(struct clk_gate_data) {                        \
        .offset = (_reg),                                    \
        .bit_idx = (_bit),                                   \
        .flags = 0,                                          \
    },                                                       \
    .hw.init = &(struct clk_init_data) {                     \
        .name = #_name,                                      \
        .ops = &clk_regmap_gate_ro_ops,                      \
        .parent_clks = (const struct clk *[]) {              \
            &g12a_clk81,                                     \
        },                                                   \
        .num_parents = 1,                                    \
        .flags = 0,                                          \
    },                                                       \
}

/* Everything Else (EE) domain gates */
static MESON_CLK81_GATE(g12a_ddr,               HHI_GCLK_MPEG0,    0);
static MESON_CLK81_GATE(g12a_dos,               HHI_GCLK_MPEG0,    1);
static MESON_CLK81_GATE(g12a_audio_locker,      HHI_GCLK_MPEG0,    2);
static MESON_CLK81_GATE(g12a_mipi_dsi_host,     HHI_GCLK_MPEG0,    3);
static MESON_CLK81_GATE(g12a_eth_phy,           HHI_GCLK_MPEG0,    4);
static MESON_CLK81_GATE(g12a_isa,               HHI_GCLK_MPEG0,    5);
static MESON_CLK81_GATE(g12a_pl301,             HHI_GCLK_MPEG0,    6);
static MESON_CLK81_GATE(g12a_periphs,           HHI_GCLK_MPEG0,    7);
static MESON_CLK81_GATE(g12a_spicc_0,           HHI_GCLK_MPEG0,    8);
static MESON_CLK81_GATE(g12a_i2c,            HHI_GCLK_MPEG0,    9);
static MESON_CLK81_GATE(g12a_sana,            HHI_GCLK_MPEG0,    10);
static MESON_CLK81_GATE(g12a_sd,            HHI_GCLK_MPEG0,    11);
static MESON_CLK81_GATE(g12a_rng0,            HHI_GCLK_MPEG0,    12);
static MESON_CLK81_GATE(g12a_uart0,            HHI_GCLK_MPEG0,    13);
static MESON_CLK81_GATE(g12a_spicc_1,            HHI_GCLK_MPEG0,    14);
static MESON_CLK81_GATE(g12a_hiu_reg,            HHI_GCLK_MPEG0,    19);
static MESON_CLK81_GATE(g12a_mipi_dsi_phy,        HHI_GCLK_MPEG0,    20);
static MESON_CLK81_GATE(g12a_assist_misc,        HHI_GCLK_MPEG0,    23);
static MESON_CLK81_GATE(g12a_emmc_a,            HHI_GCLK_MPEG0,    4);
static MESON_CLK81_GATE(g12a_emmc_b,            HHI_GCLK_MPEG0,    25);
static MESON_CLK81_GATE(g12a_emmc_c,            HHI_GCLK_MPEG0,    26);
static MESON_CLK81_GATE(g12a_audio_codec,        HHI_GCLK_MPEG0,    28);

static MESON_CLK81_GATE(g12a_audio,            HHI_GCLK_MPEG1,    0);
static MESON_CLK81_GATE(g12a_eth_core,        HHI_GCLK_MPEG1,    3);
static MESON_CLK81_GATE(g12a_demux,            HHI_GCLK_MPEG1,    4);
static MESON_CLK81_GATE(g12a_audio_ififo,        HHI_GCLK_MPEG1,    11);
static MESON_CLK81_GATE(g12a_adc,            HHI_GCLK_MPEG1,    13);
static MESON_CLK81_GATE(g12a_uart1,            HHI_GCLK_MPEG1,    16);
static MESON_CLK81_GATE(g12a_g2d,            HHI_GCLK_MPEG1,    20);
static MESON_CLK81_GATE(g12a_reset,            HHI_GCLK_MPEG1,    23);
static MESON_CLK81_GATE(g12a_pcie_comb,        HHI_GCLK_MPEG1,    24);
static MESON_CLK81_GATE(g12a_parser,            HHI_GCLK_MPEG1,    25);
static MESON_CLK81_GATE(g12a_usb_general,        HHI_GCLK_MPEG1,    26);
static MESON_CLK81_GATE(g12a_pcie_phy,        HHI_GCLK_MPEG1,    27);
static MESON_CLK81_GATE(g12a_ahb_arb0,        HHI_GCLK_MPEG1,    29);

static MESON_CLK81_GATE(g12a_ahb_data_bus,        HHI_GCLK_MPEG2,    1);
static MESON_CLK81_GATE(g12a_ahb_ctrl_bus,        HHI_GCLK_MPEG2,    2);
static MESON_CLK81_GATE(g12a_htx_hdcp22,        HHI_GCLK_MPEG2,    3);
static MESON_CLK81_GATE(g12a_htx_pclk,        HHI_GCLK_MPEG2,    4);
static MESON_CLK81_GATE(g12a_bt656,            HHI_GCLK_MPEG2,    6);
static MESON_CLK81_GATE(g12a_usb1_to_ddr,        HHI_GCLK_MPEG2,    8);
static MESON_CLK81_GATE(g12b_mipi_isp_gate,        HHI_GCLK_MPEG2,    17);
static MESON_CLK81_GATE(g12a_mmc_pclk,        HHI_GCLK_MPEG2,    11);
static MESON_CLK81_GATE(g12a_uart2,            HHI_GCLK_MPEG2,    15);
static MESON_CLK81_GATE(g12a_vpu_intr,        HHI_GCLK_MPEG2,    25);
static MESON_CLK81_GATE(g12b_csi_phy1,        HHI_GCLK_MPEG2,    28);
static MESON_CLK81_GATE(g12b_csi_phy0,        HHI_GCLK_MPEG2,    29);
static MESON_CLK81_GATE(g12a_gic,            HHI_GCLK_MPEG2,    30);

static MESON_CLK81_GATE(g12a_vclk2_venci0,        HHI_GCLK_OTHER,    1);
static MESON_CLK81_GATE(g12a_vclk2_venci1,        HHI_GCLK_OTHER,    2);
static MESON_CLK81_GATE(g12a_vclk2_vencp0,        HHI_GCLK_OTHER,    3);
static MESON_CLK81_GATE(g12a_vclk2_vencp1,        HHI_GCLK_OTHER,    4);
static MESON_CLK81_GATE(g12a_vclk2_venct0,        HHI_GCLK_OTHER,    5);
static MESON_CLK81_GATE(g12a_vclk2_venct1,        HHI_GCLK_OTHER,    6);
static MESON_CLK81_GATE(g12a_vclk2_other,        HHI_GCLK_OTHER,    7);
static MESON_CLK81_GATE(g12a_vclk2_enci,        HHI_GCLK_OTHER,    8);
static MESON_CLK81_GATE(g12a_vclk2_encp,        HHI_GCLK_OTHER,    9);
static MESON_CLK81_GATE(g12a_dac_clk,            HHI_GCLK_OTHER,    10);
static MESON_CLK81_GATE(g12a_aoclk_gate,        HHI_GCLK_OTHER,    14);
static MESON_CLK81_GATE(g12a_iec958_gate,        HHI_GCLK_OTHER,    16);
static MESON_CLK81_GATE(g12a_enc480p,            HHI_GCLK_OTHER,    20);
static MESON_CLK81_GATE(g12a_rng1,            HHI_GCLK_OTHER,    21);
static MESON_CLK81_GATE(g12a_vclk2_enct,        HHI_GCLK_OTHER,    22);
static MESON_CLK81_GATE(g12a_vclk2_encl,        HHI_GCLK_OTHER,    23);
static MESON_CLK81_GATE(g12a_vclk2_venclmmc,        HHI_GCLK_OTHER,    24);
static MESON_CLK81_GATE(g12a_vclk2_vencl,        HHI_GCLK_OTHER,    25);
static MESON_CLK81_GATE(g12a_vclk2_other1,        HHI_GCLK_OTHER,    26);

static MESON_CLK81_GATE_RO(g12a_dma,            HHI_GCLK_OTHER2, 0);
static MESON_CLK81_GATE_RO(g12a_efuse,        HHI_GCLK_OTHER2, 1);
static MESON_CLK81_GATE_RO(g12a_rom_boot,        HHI_GCLK_OTHER2, 2);
static MESON_CLK81_GATE_RO(g12a_reset_sec,        HHI_GCLK_OTHER2, 3);
static MESON_CLK81_GATE_RO(g12a_sec_ahb_apb3,        HHI_GCLK_OTHER2, 4);

static struct clk *sm1_clks[] = {
    /* [CLKID_SYS_PLL]            = &g12a_sys_pll, */
    [CLKID_FIXED_PLL]        = &g12a_fixed_pll,
    [CLKID_FCLK_DIV2]        = &g12a_fclk_div2,
    [CLKID_FCLK_DIV3]        = &g12a_fclk_div3,
    [CLKID_FCLK_DIV4]        = &g12a_fclk_div4,
    [CLKID_FCLK_DIV5]        = &g12a_fclk_div5,
    [CLKID_FCLK_DIV7]        = &g12a_fclk_div7,
    /* [CLKID_FCLK_DIV2P5]        = &g12a_fclk_div2p5, */
    /* [CLKID_GP0_PLL]            = &g12a_gp0_pll, */
    [CLKID_MPEG_SEL]        = &g12a_mpeg_clk_sel,
    [CLKID_MPEG_DIV]        = &g12a_mpeg_clk_div,
    [CLKID_CLK81]            = &g12a_clk81,
    [CLKID_MPLL0]            = &g12a_mpll0,
    [CLKID_MPLL1]            = &g12a_mpll1,
    [CLKID_MPLL2]            = &g12a_mpll2,
    [CLKID_MPLL3]            = &g12a_mpll3,
    [CLKID_DDR]            = &g12a_ddr,
    [CLKID_DOS]            = &g12a_dos,
    [CLKID_AUDIO_LOCKER]        = &g12a_audio_locker,
    [CLKID_MIPI_DSI_HOST]        = &g12a_mipi_dsi_host,
    [CLKID_ETH_PHY]            = &g12a_eth_phy,
    [CLKID_ISA]            = &g12a_isa,
    [CLKID_PL301]            = &g12a_pl301,
    [CLKID_PERIPHS]            = &g12a_periphs,
    [CLKID_SPICC0]            = &g12a_spicc_0,
    [CLKID_I2C]            = &g12a_i2c,
    [CLKID_SANA]            = &g12a_sana,
    [CLKID_SD]            = &g12a_sd,
    [CLKID_RNG0]            = &g12a_rng0,
    [CLKID_UART0]            = &g12a_uart0,
    [CLKID_SPICC1]            = &g12a_spicc_1,
    [CLKID_HIU_IFACE]        = &g12a_hiu_reg,
    [CLKID_MIPI_DSI_PHY]        = &g12a_mipi_dsi_phy,
    [CLKID_ASSIST_MISC]        = &g12a_assist_misc,
    [CLKID_SD_EMMC_A]        = &g12a_emmc_a,
    [CLKID_SD_EMMC_B]        = &g12a_emmc_b,
    [CLKID_SD_EMMC_C]        = &g12a_emmc_c,
    [CLKID_AUDIO_CODEC]        = &g12a_audio_codec,
    [CLKID_AUDIO]            = &g12a_audio,
    [CLKID_ETH]            = &g12a_eth_core,
    [CLKID_DEMUX]            = &g12a_demux,
    [CLKID_AUDIO_IFIFO]        = &g12a_audio_ififo,
    [CLKID_ADC]            = &g12a_adc,
    [CLKID_UART1]            = &g12a_uart1,
    [CLKID_G2D]            = &g12a_g2d,
    [CLKID_RESET]            = &g12a_reset,
    [CLKID_PCIE_COMB]        = &g12a_pcie_comb,
    [CLKID_PARSER]            = &g12a_parser,
    [CLKID_USB]            = &g12a_usb_general,
    [CLKID_PCIE_PHY]        = &g12a_pcie_phy,
    [CLKID_AHB_ARB0]        = &g12a_ahb_arb0,
    [CLKID_AHB_DATA_BUS]        = &g12a_ahb_data_bus,
    [CLKID_AHB_CTRL_BUS]        = &g12a_ahb_ctrl_bus,
    [CLKID_HTX_HDCP22]        = &g12a_htx_hdcp22,
    [CLKID_HTX_PCLK]        = &g12a_htx_pclk,
    [CLKID_BT656]            = &g12a_bt656,
    [CLKID_USB1_DDR_BRIDGE]        = &g12a_usb1_to_ddr,
    [CLKID_MMC_PCLK]        = &g12a_mmc_pclk,
    [CLKID_UART2]            = &g12a_uart2,
    [CLKID_VPU_INTR]        = &g12a_vpu_intr,
    [CLKID_GIC]            = &g12a_gic,
    /* [CLKID_SD_EMMC_A_CLK0_SEL]    = &g12a_sd_emmc_a_clk0_sel, */
    /* [CLKID_SD_EMMC_A_CLK0_DIV]    = &g12a_sd_emmc_a_clk0_div, */
    /* [CLKID_SD_EMMC_A_CLK0]        = &g12a_sd_emmc_a_clk0, */
    /* [CLKID_SD_EMMC_B_CLK0_SEL]    = &g12a_sd_emmc_b_clk0_sel, */
    /* [CLKID_SD_EMMC_B_CLK0_DIV]    = &g12a_sd_emmc_b_clk0_div, */
    /* [CLKID_SD_EMMC_B_CLK0]        = &g12a_sd_emmc_b_clk0, */
    /* [CLKID_SD_EMMC_C_CLK0_SEL]    = &g12a_sd_emmc_c_clk0_sel, */
    /* [CLKID_SD_EMMC_C_CLK0_DIV]    = &g12a_sd_emmc_c_clk0_div, */
    /* [CLKID_SD_EMMC_C_CLK0]        = &g12a_sd_emmc_c_clk0, */
    [CLKID_MPLL0_DIV]        = &g12a_mpll0_div,
    [CLKID_MPLL1_DIV]        = &g12a_mpll1_div,
    [CLKID_MPLL2_DIV]        = &g12a_mpll2_div,
    [CLKID_MPLL3_DIV]        = &g12a_mpll3_div,
    [CLKID_FCLK_DIV2_DIV]        = &g12a_fclk_div2_div,
    [CLKID_FCLK_DIV3_DIV]        = &g12a_fclk_div3_div,
    [CLKID_FCLK_DIV4_DIV]        = &g12a_fclk_div4_div,
    [CLKID_FCLK_DIV5_DIV]        = &g12a_fclk_div5_div,
    [CLKID_FCLK_DIV7_DIV]        = &g12a_fclk_div7_div,
    /* [CLKID_FCLK_DIV2P5_DIV]        = &g12a_fclk_div2p5_div, */
    /* [CLKID_HIFI_PLL]        = &g12a_hifi_pll, */
    [CLKID_VCLK2_VENCI0]        = &g12a_vclk2_venci0,
    [CLKID_VCLK2_VENCI1]        = &g12a_vclk2_venci1,
    [CLKID_VCLK2_VENCP0]        = &g12a_vclk2_vencp0,
    [CLKID_VCLK2_VENCP1]        = &g12a_vclk2_vencp1,
    [CLKID_VCLK2_VENCT0]        = &g12a_vclk2_venct0,
    [CLKID_VCLK2_VENCT1]        = &g12a_vclk2_venct1,
    [CLKID_VCLK2_OTHER]        = &g12a_vclk2_other,
    [CLKID_VCLK2_ENCI]        = &g12a_vclk2_enci,
    [CLKID_VCLK2_ENCP]        = &g12a_vclk2_encp,
    [CLKID_DAC_CLK]            = &g12a_dac_clk,
    [CLKID_AOCLK]            = &g12a_aoclk_gate,
    [CLKID_IEC958]            = &g12a_iec958_gate,
    [CLKID_ENC480P]            = &g12a_enc480p,
    [CLKID_RNG1]            = &g12a_rng1,
    [CLKID_VCLK2_ENCT]        = &g12a_vclk2_enct,
    [CLKID_VCLK2_ENCL]        = &g12a_vclk2_encl,
    [CLKID_VCLK2_VENCLMMC]        = &g12a_vclk2_venclmmc,
    [CLKID_VCLK2_VENCL]        = &g12a_vclk2_vencl,
    [CLKID_VCLK2_OTHER1]        = &g12a_vclk2_other1,
    [CLKID_FIXED_PLL_DCO]        = &g12a_fixed_pll_dco,
    /* [CLKID_SYS_PLL_DCO]        = &g12a_sys_pll_dco, */
    /* [CLKID_GP0_PLL_DCO]        = &g12a_gp0_pll_dco, */
    /* [CLKID_HIFI_PLL_DCO]        = &g12a_hifi_pll_dco, */
    [CLKID_DMA]            = &g12a_dma,
    [CLKID_EFUSE]            = &g12a_efuse,
    [CLKID_ROM_BOOT]        = &g12a_rom_boot,
    [CLKID_RESET_SEC]        = &g12a_reset_sec,
    [CLKID_SEC_AHB_APB3]        = &g12a_sec_ahb_apb3,
    [CLKID_MPLL_PREDIV]        = &g12a_mpll_prediv,
    /* [CLKID_VPU_0_SEL]        = &g12a_vpu_0_sel, */
    /* [CLKID_VPU_0_DIV]        = &g12a_vpu_0_div, */
    /* [CLKID_VPU_0]            = &g12a_vpu_0, */
    /* [CLKID_VPU_1_SEL]        = &g12a_vpu_1_sel, */
    /* [CLKID_VPU_1_DIV]        = &g12a_vpu_1_div, */
    /* [CLKID_VPU_1]            = &g12a_vpu_1, */
    /* [CLKID_VPU]            = &g12a_vpu, */
    /* [CLKID_VAPB_0_SEL]        = &g12a_vapb_0_sel, */
    /* [CLKID_VAPB_0_DIV]        = &g12a_vapb_0_div, */
    /* [CLKID_VAPB_0]            = &g12a_vapb_0, */
    /* [CLKID_VAPB_1_SEL]        = &g12a_vapb_1_sel, */
    /* [CLKID_VAPB_1_DIV]        = &g12a_vapb_1_div, */
    /* [CLKID_VAPB_1]            = &g12a_vapb_1, */
    /* [CLKID_VAPB_SEL]        = &g12a_vapb_sel, */
    /* [CLKID_VAPB]            = &g12a_vapb, */
    /* [CLKID_HDMI_PLL_DCO]        = &g12a_hdmi_pll_dco, */
    /* [CLKID_HDMI_PLL_OD]        = &g12a_hdmi_pll_od, */
    /* [CLKID_HDMI_PLL_OD2]        = &g12a_hdmi_pll_od2, */
    /* [CLKID_HDMI_PLL]        = &g12a_hdmi_pll, */
    /* [CLKID_VID_PLL]            = &g12a_vid_pll_div, */
    /* [CLKID_VID_PLL_SEL]        = &g12a_vid_pll_sel, */
    /* [CLKID_VID_PLL_DIV]        = &g12a_vid_pll, */
    /* [CLKID_VCLK_SEL]        = &g12a_vclk_sel, */
    /* [CLKID_VCLK2_SEL]        = &g12a_vclk2_sel, */
    /* [CLKID_VCLK_INPUT]        = &g12a_vclk_input, */
    /* [CLKID_VCLK2_INPUT]        = &g12a_vclk2_input, */
    /* [CLKID_VCLK_DIV]        = &g12a_vclk_div, */
    /* [CLKID_VCLK2_DIV]        = &g12a_vclk2_div, */
    /* [CLKID_VCLK]            = &g12a_vclk, */
    /* [CLKID_VCLK2]            = &g12a_vclk2, */
    /* [CLKID_VCLK_DIV1]        = &g12a_vclk_div1, */
    /* [CLKID_VCLK_DIV2_EN]        = &g12a_vclk_div2_en, */
    /* [CLKID_VCLK_DIV4_EN]        = &g12a_vclk_div4_en, */
    /* [CLKID_VCLK_DIV6_EN]        = &g12a_vclk_div6_en, */
    /* [CLKID_VCLK_DIV12_EN]        = &g12a_vclk_div12_en, */
    /* [CLKID_VCLK2_DIV1]        = &g12a_vclk2_div1, */
    /* [CLKID_VCLK2_DIV2_EN]        = &g12a_vclk2_div2_en, */
    /* [CLKID_VCLK2_DIV4_EN]        = &g12a_vclk2_div4_en, */
    /* [CLKID_VCLK2_DIV6_EN]        = &g12a_vclk2_div6_en, */
    /* [CLKID_VCLK2_DIV12_EN]        = &g12a_vclk2_div12_en, */
    /* [CLKID_VCLK_DIV2]        = &g12a_vclk_div2, */
    /* [CLKID_VCLK_DIV4]        = &g12a_vclk_div4, */
    /* [CLKID_VCLK_DIV6]        = &g12a_vclk_div6, */
    /* [CLKID_VCLK_DIV12]        = &g12a_vclk_div12, */
    /* [CLKID_VCLK2_DIV2]        = &g12a_vclk2_div2, */
    /* [CLKID_VCLK2_DIV4]        = &g12a_vclk2_div4, */
    /* [CLKID_VCLK2_DIV6]        = &g12a_vclk2_div6, */
    /* [CLKID_VCLK2_DIV12]        = &g12a_vclk2_div12, */
    /* [CLKID_CTS_ENCI_SEL]        = &g12a_cts_enci_sel, */
    /* [CLKID_CTS_ENCP_SEL]        = &g12a_cts_encp_sel, */
    /* [CLKID_CTS_ENCL_SEL]        = &g12a_cts_encl_sel, */
    /* [CLKID_CTS_VDAC_SEL]        = &g12a_cts_vdac_sel, */
    /* [CLKID_HDMI_TX_SEL]        = &g12a_hdmi_tx_sel, */
    /* [CLKID_CTS_ENCI]        = &g12a_cts_enci, */
    /* [CLKID_CTS_ENCP]        = &g12a_cts_encp, */
    /* [CLKID_CTS_ENCL]        = &g12a_cts_encl, */
    /* [CLKID_CTS_VDAC]        = &g12a_cts_vdac, */
    /* [CLKID_HDMI_TX]            = &g12a_hdmi_tx, */
    /* [CLKID_HDMI_SEL]        = &g12a_hdmi_sel, */
    /* [CLKID_HDMI_DIV]        = &g12a_hdmi_div, */
    [CLKID_HDMI]            = &g12a_hdmi,
    /* [CLKID_MALI_0_SEL]        = &g12a_mali_0_sel, */
    /* [CLKID_MALI_0_DIV]        = &g12a_mali_0_div, */
    /* [CLKID_MALI_0]            = &g12a_mali_0, */
    /* [CLKID_MALI_1_SEL]        = &g12a_mali_1_sel, */
    /* [CLKID_MALI_1_DIV]        = &g12a_mali_1_div, */
    /* [CLKID_MALI_1]            = &g12a_mali_1, */
    /* [CLKID_MALI]            = &g12a_mali, */
    /* [CLKID_MPLL_50M_DIV]        = &g12a_mpll_50m_div, */
    /* [CLKID_MPLL_50M]        = &g12a_mpll_50m, */
    /* [CLKID_SYS_PLL_DIV16_EN]    = &g12a_sys_pll_div16_en, */
    /* [CLKID_SYS_PLL_DIV16]        = &g12a_sys_pll_div16, */
    /* [CLKID_CPU_CLK_DYN0_SEL]    = &g12a_cpu_clk_premux0, */
    /* [CLKID_CPU_CLK_DYN0_DIV]    = &g12a_cpu_clk_mux0_div, */
    /* [CLKID_CPU_CLK_DYN0]        = &g12a_cpu_clk_postmux0, */
    /* [CLKID_CPU_CLK_DYN1_SEL]    = &g12a_cpu_clk_premux1, */
    /* [CLKID_CPU_CLK_DYN1_DIV]    = &g12a_cpu_clk_mux1_div, */
    /* [CLKID_CPU_CLK_DYN1]        = &g12a_cpu_clk_postmux1, */
    /* [CLKID_CPU_CLK_DYN]        = &g12a_cpu_clk_dyn, */
    /* [CLKID_CPU_CLK]            = &g12a_cpu_clk, */
    /* [CLKID_CPU_CLK_DIV16_EN]    = &g12a_cpu_clk_div16_en, */
    /* [CLKID_CPU_CLK_DIV16]        = &g12a_cpu_clk_div16, */
    /* [CLKID_CPU_CLK_APB_DIV]        = &g12a_cpu_clk_apb_div, */
    /* [CLKID_CPU_CLK_APB]        = &g12a_cpu_clk_apb, */
    /* [CLKID_CPU_CLK_ATB_DIV]        = &g12a_cpu_clk_atb_div, */
    /* [CLKID_CPU_CLK_ATB]        = &g12a_cpu_clk_atb, */
    /* [CLKID_CPU_CLK_AXI_DIV]        = &g12a_cpu_clk_axi_div, */
    /* [CLKID_CPU_CLK_AXI]        = &g12a_cpu_clk_axi, */
    /* [CLKID_CPU_CLK_TRACE_DIV]    = &g12a_cpu_clk_trace_div, */
    /* [CLKID_CPU_CLK_TRACE]        = &g12a_cpu_clk_trace, */
    /* [CLKID_PCIE_PLL_DCO]        = &g12a_pcie_pll_dco, */
    /* [CLKID_PCIE_PLL_DCO_DIV2]    = &g12a_pcie_pll_dco_div2, */
    /* [CLKID_PCIE_PLL_OD]        = &g12a_pcie_pll_od, */
    /* [CLKID_PCIE_PLL]        = &g12a_pcie_pll, */
    /* [CLKID_VDEC_1_SEL]        = &g12a_vdec_1_sel, */
    /* [CLKID_VDEC_1_DIV]        = &g12a_vdec_1_div, */
    /* [CLKID_VDEC_1]            = &g12a_vdec_1, */
    /* [CLKID_VDEC_HEVC_SEL]        = &g12a_vdec_hevc_sel, */
    /* [CLKID_VDEC_HEVC_DIV]        = &g12a_vdec_hevc_div, */
    /* [CLKID_VDEC_HEVC]        = &g12a_vdec_hevc, */
    /* [CLKID_VDEC_HEVCF_SEL]        = &g12a_vdec_hevcf_sel, */
    /* [CLKID_VDEC_HEVCF_DIV]        = &g12a_vdec_hevcf_div, */
    /* [CLKID_VDEC_HEVCF]        = &g12a_vdec_hevcf, */
    /* [CLKID_TS_DIV]            = &g12a_ts_div, */
    /* [CLKID_TS]            = &g12a_ts, */
    /* [CLKID_GP1_PLL_DCO]        = &sm1_gp1_pll_dco, */
    /* [CLKID_GP1_PLL]            = &sm1_gp1_pll, */
    /* [CLKID_DSU_CLK_DYN0_SEL]    = &sm1_dsu_clk_premux0, */
    /* [CLKID_DSU_CLK_DYN0_DIV]    = &sm1_dsu_clk_premux1, */
    /* [CLKID_DSU_CLK_DYN0]        = &sm1_dsu_clk_mux0_div, */
    /* [CLKID_DSU_CLK_DYN1_SEL]    = &sm1_dsu_clk_postmux0, */
    /* [CLKID_DSU_CLK_DYN1_DIV]    = &sm1_dsu_clk_mux1_div, */
    /* [CLKID_DSU_CLK_DYN1]        = &sm1_dsu_clk_postmux1, */
    /* [CLKID_DSU_CLK_DYN]        = &sm1_dsu_clk_dyn, */
    /* [CLKID_DSU_CLK_FINAL]        = &sm1_dsu_final_clk, */
    /* [CLKID_DSU_CLK]            = &sm1_dsu_clk, */
    /* [CLKID_CPU1_CLK]        = &sm1_cpu1_clk, */
    /* [CLKID_CPU2_CLK]        = &sm1_cpu2_clk, */
    /* [CLKID_CPU3_CLK]        = &sm1_cpu3_clk, */
    /* [CLKID_SPICC0_SCLK_SEL]        = &g12a_spicc0_sclk_sel, */
    /* [CLKID_SPICC0_SCLK_DIV]        = &g12a_spicc0_sclk_div, */
    /* [CLKID_SPICC0_SCLK]        = &g12a_spicc0_sclk, */
    /* [CLKID_SPICC1_SCLK_SEL]        = &g12a_spicc1_sclk_sel, */
    /* [CLKID_SPICC1_SCLK_DIV]        = &g12a_spicc1_sclk_div, */
    /* [CLKID_SPICC1_SCLK]        = &g12a_spicc1_sclk, */
    /* [CLKID_NNA_AXI_CLK_SEL]        = &sm1_nna_axi_clk_sel, */
    /* [CLKID_NNA_AXI_CLK_DIV]        = &sm1_nna_axi_clk_div, */
    /* [CLKID_NNA_AXI_CLK]        = &sm1_nna_axi_clk, */
    /* [CLKID_NNA_CORE_CLK_SEL]    = &sm1_nna_core_clk_sel, */
    /* [CLKID_NNA_CORE_CLK_DIV]    = &sm1_nna_core_clk_div, */
    /* [CLKID_NNA_CORE_CLK]        = &sm1_nna_core_clk, */
    /* [CLKID_MIPI_DSI_PXCLK_SEL]    = &g12a_mipi_dsi_pxclk_sel, */
    /* [CLKID_MIPI_DSI_PXCLK_DIV]    = &g12a_mipi_dsi_pxclk_div, */
    /* [CLKID_MIPI_DSI_PXCLK]        = &g12a_mipi_dsi_pxclk, */
};


unsigned long clk_recalc_rate(struct clk *clk)
{
    const struct clk_init_data *init = (struct clk_init_data *)clk->hw.init;
    uint32_t num_parents = init->num_parents;
    unsigned long parent_rate = 1;

    if (init->parent_data) {
        uint8_t parent_idx = num_parents > 1 ? init->ops->get_parent(clk) : 0;
        struct clk_parent_data parent_data = init->parent_data[parent_idx];

        if (parent_data.clk) {
            struct clk *parent_clk = parent_data.clk;
            parent_rate = clk_recalc_rate(parent_clk);
        } else if (sddf_strcmp(parent_data.fw_name, "xtal") == 0) {
            /* TODO: Replace this with an hw structure */
            parent_rate = 24000000;
        }
    } else {
        struct clk *parent_clk = init->parent_clks[0];
        parent_rate = clk_recalc_rate(parent_clk);
    }

    sddf_dprintf("Clock: %s, parent rate: %lu", init->name, parent_rate);
    unsigned long rate = parent_rate;
    if (init->ops->recalc_rate) {
        rate = init->ops->recalc_rate(clk, parent_rate);
    }
    sddf_dprintf(" => rate: %lu\n", rate);

    return rate;
}

void notified(microkit_channel ch)
{

}

void init(void)
{
    init_clk_base(clk_regs);

    sddf_dprintf("-----------------\n");
    volatile uint32_t *clk_i2c_ptr = ((void *)clk_regs + I2C_CLK_OFFSET);

    sddf_dprintf("Clock driver initialising...\n");

    /* for (int i = 0; i < NUM_DEVICE_CLKS; i++) { */
        /* struct clk *clk = sm1_clks[enabled_hw_clks[i]->clk_id]; */
        /* clk->hw.init->ops->enable(clk); */
    /* } */

    // Check that registers actually changed
    if (!(*clk_i2c_ptr & I2C_CLK_BIT)) {
        sddf_dprintf("failed to toggle clock!\n");
    }

    sddf_dprintf("-----------------\n");

    struct clk *mpeg_sel = sm1_clks[CLKID_MPEG_SEL];
    int ret = mpeg_sel->hw.init->ops->set_parent(mpeg_sel, 6);
    uint64_t rate = clk_recalc_rate(mpeg_sel);
    sddf_dprintf("MEPG_SEL clock rate: %lu\n", rate);

    /*     CLKID_MPLL2    0x11940000 */
    /*     CLKID_MPLL0    0x10266000 */
    /*     CLKID_MPLL1 0x17700000 */
	struct clk *parent_clk = sm1_clks[CLKID_MPLL_PREDIV];
    uint64_t prate = clk_recalc_rate(parent_clk);
    sddf_dprintf("%s rate: %lu\n", parent_clk->hw.init->name, rate);

    struct clk *test_clk = sm1_clks[CLKID_MPLL0_DIV];
	test_clk->hw.init->ops->init(test_clk);
    rate = clk_recalc_rate(test_clk);
    sddf_dprintf("%s rate: %lu\n", test_clk->hw.init->name, rate);
	test_clk->hw.init->ops->set_rate(test_clk, 0x10266000, prate);
    rate = clk_recalc_rate(test_clk);
    sddf_dprintf("%s rate: %lu\n", test_clk->hw.init->name, rate);

    clk_msr_stat();

   sddf_dprintf("-----------------\n");
}
