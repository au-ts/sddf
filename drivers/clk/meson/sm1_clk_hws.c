#include <clk.h>
#include <g12a-clkc.h>
#include <sm1_clk_hws.h>
#include <clk-operations.h>
#include <sddf/util/util.h>

const struct clk g12a_xtal = {
    .data = &(struct clk_source_data){
        .rate = 24000000,
    },
    .hw.init = &(struct clk_init_data){
        .name = "xtal",
        .ops = &meson_clk_source_ops,
    }
};

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
static MESON_DIV_RO(g12a_fixed_pll, HHI_FIX_PLL_CNTL0, 16, 2, CLK_DIVIDER_POWER_OF_TWO, { &g12a_fixed_pll_dco }, 1, 0);
static struct clk g12a_sys_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_SYS_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_SYS_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_SYS_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .l = {
            .reg_off = HHI_SYS_PLL_CNTL0,
            .shift   = 31,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_SYS_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
        .range_min = 128,
        .range_max = 250,
    },
    .hw.init = &(struct clk_init_data){
        .name = "sys_pll_dco",
        .ops = &meson_clk_pll_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
        /* This clock feeds the CPU, avoid disabling it */
        .flags = CLK_IS_CRITICAL,
    },
};
static MESON_DIV(g12a_sys_pll, HHI_SYS_PLL_CNTL0, 16, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_sys_pll_dco }, 1, 0);
static MESON_GATE_RO(g12a_sys_pll_div16_en, HHI_SYS_CPU_CLK_CNTL1, 24, 0, { &g12a_sys_pll }, 1, 0);
static MESON_FIXED_FACTOR(g12a_sys_pll_div16, 1, 16, { &g12a_sys_pll_div16_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div2_div, 1, 2, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div2, HHI_FIX_PLL_CNTL1, 24, 0, { &g12a_fclk_div2_div }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div3_div, 1, 3, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div3, HHI_FIX_PLL_CNTL1, 20, 0, { &g12a_fclk_div3_div }, 1, 0);
const struct clk_parent_data g12a_cpu_clk_premux0_parent_table[] = {
            { .fw_name = "xtal", },
            { .clk = &g12a_fclk_div2 },
            { .clk = &g12a_fclk_div3 },
};
static MESON_MUX(g12a_cpu_clk_premux0, HHI_SYS_CPU_CLK_CNTL0, 0x3, 0, 0, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_premux0_parent_table, 3, 0);
const struct clk_parent_data g12a_cpu_clk_premux1_parent_table[] = {
            { .fw_name = "xtal", },
            { .clk = &g12a_fclk_div2 },
            { .clk = &g12a_fclk_div3 },
};
static MESON_MUX(g12a_cpu_clk_premux1, HHI_SYS_CPU_CLK_CNTL0, 0x3, 16, 0, 0, g12a_cpu_clk_premux1_parent_table, 3, 0);
static struct clk g12a_cpu_clk_mux0_div = {
    .data = &(struct meson_clk_cpu_dyndiv_data){
        .div = {
            .reg_off = HHI_SYS_CPU_CLK_CNTL0,
            .shift = 4,
            .width = 6,
        },
        .dyn = {
            .reg_off = HHI_SYS_CPU_CLK_CNTL0,
            .shift = 26,
            .width = 1,
        },
    },
    .hw.init = &(struct clk_init_data){
        .name = "cpu_clk_dyn0_div",
        .ops = &meson_clk_cpu_dyndiv_ops,
        .parent_clks = (const struct clk *[]) {
            &g12a_cpu_clk_premux0
        },
        .num_parents = 1,
        .flags = CLK_SET_RATE_PARENT,
    },
};
const struct clk_parent_data g12a_cpu_clk_postmux0_parent_table[] = {
    { .clk = &g12a_cpu_clk_premux0 },
    { .clk = &g12a_cpu_clk_mux0_div },
};
static MESON_MUX(g12a_cpu_clk_postmux0, HHI_SYS_CPU_CLK_CNTL0, 0x1, 2, 0, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_postmux0_parent_table, 2, 0);
static MESON_DIV_RO(g12a_cpu_clk_mux1_div, HHI_SYS_CPU_CLK_CNTL0, 20, 6, 0, { &g12a_cpu_clk_premux1 }, 1, 0);
const struct clk_parent_data g12a_cpu_clk_postmux1_parent_table[] = {
    { .clk = &g12a_cpu_clk_premux1 },
    { .clk = &g12a_cpu_clk_mux1_div },
};
static MESON_MUX(g12a_cpu_clk_postmux1, HHI_SYS_CPU_CLK_CNTL0, 0x1, 18, 0, 0, g12a_cpu_clk_postmux1_parent_table, 2, 0);
const struct clk_parent_data g12a_cpu_clk_dyn_parent_table[] = {
    { .clk = &g12a_cpu_clk_postmux0 },
    { .clk = &g12a_cpu_clk_postmux1 },
};
static MESON_MUX(g12a_cpu_clk_dyn, HHI_SYS_CPU_CLK_CNTL0, 0x1, 10, 0, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_dyn_parent_table, 2, 0);
const struct clk_parent_data g12a_cpu_clk_parent_table[] = {
    { .clk = &g12a_cpu_clk_dyn },
    { .clk = &g12a_sys_pll },
};
static MESON_MUX(g12a_cpu_clk, HHI_SYS_CPU_CLK_CNTL0, 0x1, 11, 0, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_parent_table, 2, 0);


static const struct reg_sequence g12a_gp0_init_regs[] = {
    { .reg = HHI_GP0_PLL_CNTL1,    .def = 0x00000000 },
    { .reg = HHI_GP0_PLL_CNTL2,    .def = 0x00000000 },
    { .reg = HHI_GP0_PLL_CNTL3,    .def = 0x48681c00 },
    { .reg = HHI_GP0_PLL_CNTL4,    .def = 0x33771290 },
    { .reg = HHI_GP0_PLL_CNTL5,    .def = 0x39272000 },
    { .reg = HHI_GP0_PLL_CNTL6,    .def = 0x56540000 },
};
static struct clk g12a_gp0_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_GP0_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_GP0_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_GP0_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .frac = {
            .reg_off = HHI_GP0_PLL_CNTL1,
            .shift   = 0,
            .width   = 17,
        },
        .l = {
            .reg_off = HHI_GP0_PLL_CNTL0,
            .shift   = 31,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_GP0_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
        .range_min = 125,
        .range_max = 255,
        .init_regs = g12a_gp0_init_regs,
        .init_count = ARRAY_SIZE(g12a_gp0_init_regs),
    },
    .hw.init = &(struct clk_init_data){
        .name = "gp0_pll_dco",
        .ops = &meson_clk_pll_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
    },
};
static MESON_DIV(g12a_gp0_pll, HHI_GP0_PLL_CNTL0, 16, 3, (CLK_DIVIDER_POWER_OF_TWO |
              CLK_DIVIDER_ROUND_CLOSEST), { &g12a_gp0_pll_dco }, 1, 0);
static struct clk sm1_gp1_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_GP1_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_GP1_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_GP1_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .frac = {
            .reg_off = HHI_GP1_PLL_CNTL1,
            .shift   = 0,
            .width   = 17,
        },
        .l = {
            .reg_off = HHI_GP1_PLL_CNTL0,
            .shift   = 31,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_GP1_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
    },
    .hw.init = &(struct clk_init_data){
        .name = "gp1_pll_dco",
        .ops = &meson_clk_pll_ro_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
        /* This clock feeds the DSU, avoid disabling it */
        .flags = CLK_IS_CRITICAL,
    },
};
static MESON_DIV_RO(sm1_gp1_pll, HHI_GP1_PLL_CNTL0, 16, 3, (CLK_DIVIDER_POWER_OF_TWO |
              CLK_DIVIDER_ROUND_CLOSEST), { &sm1_gp1_pll_dco }, 1, 0);

const struct clk_parent_data sm1_dsu_clk_premux0_parent_table[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div2 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &sm1_gp1_pll },
};
static MESON_MUX_RO(sm1_dsu_clk_premux0, HHI_SYS_CPU_CLK_CNTL5, 0x3, 0, 0, 0, sm1_dsu_clk_premux0_parent_table, 4, 0);
const struct clk_parent_data sm1_dsu_clk_premux1_parent_table[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div2 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &sm1_gp1_pll },
};
static MESON_MUX_RO(sm1_dsu_clk_premux1, HHI_SYS_CPU_CLK_CNTL5, 0x3, 16, 0, 0, sm1_dsu_clk_premux1_parent_table, 4, 0);
static MESON_DIV_RO(sm1_dsu_clk_mux0_div, HHI_SYS_CPU_CLK_CNTL5, 4, 6, 0, { &sm1_dsu_clk_premux0 }, 1, 0);
const struct clk_parent_data sm1_dsu_clk_postmux0_parent_table[] = {
    { .clk = &sm1_dsu_clk_premux0, },
    { .clk = &sm1_dsu_clk_mux0_div },
};
static MESON_MUX_RO(sm1_dsu_clk_postmux0, HHI_SYS_CPU_CLK_CNTL5, 0x1, 2, 0, 0, sm1_dsu_clk_postmux0_parent_table, 2, 0);
static MESON_DIV_RO(sm1_dsu_clk_mux1_div, HHI_SYS_CPU_CLK_CNTL5, 20, 6, 0, { &sm1_dsu_clk_premux1 }, 1, 0);

const struct clk_parent_data sm1_dsu_clk_postmux1_parent_table[] = {
    { .clk = &sm1_dsu_clk_premux1, },
    { .clk = &sm1_dsu_clk_mux1_div },
};
static MESON_MUX_RO(sm1_dsu_clk_postmux1, HHI_SYS_CPU_CLK_CNTL5, 0x1, 18, 0, 0, sm1_dsu_clk_postmux1_parent_table, 2, 0);
const struct clk_parent_data sm1_dsu_clk_dyn_parent_table[] = {
    { .clk = &sm1_dsu_clk_premux0, },
    { .clk = &sm1_dsu_clk_postmux1, },
};
static MESON_MUX_RO(sm1_dsu_clk_dyn, HHI_SYS_CPU_CLK_CNTL5, 0x1, 10, 0, 0, sm1_dsu_clk_dyn_parent_table, 2, 0);
const struct clk_parent_data sm1_dsu_final_clk_parent_table[] = {
    { .clk = &sm1_dsu_clk_dyn, },
    { .clk = &g12a_sys_pll, },
};
static MESON_MUX_RO(sm1_dsu_final_clk, HHI_SYS_CPU_CLK_CNTL5, 0x1, 11, 0, 0, sm1_dsu_final_clk_parent_table, 2, 0);
const struct clk_parent_data sm1_cpu_clk_parent_table[] = {
    { .clk = &g12a_cpu_clk, },
};
static MESON_MUX_RO(sm1_cpu1_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 24, 0, 0, sm1_cpu_clk_parent_table, 1, 0);
static MESON_MUX_RO(sm1_cpu2_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 25, 0, 0, sm1_cpu_clk_parent_table, 1, 0);
static MESON_MUX_RO(sm1_cpu3_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 26, 0, 0, sm1_cpu_clk_parent_table, 1, 0);
const struct clk_parent_data sm1_dsu_clk_parent_table[] = {
    { .clk = &g12a_cpu_clk, },
    { .clk = &sm1_dsu_final_clk, },
};
static MESON_MUX_RO(sm1_dsu_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 27, 0, 0, sm1_dsu_clk_parent_table, 2, 0);
static MESON_GATE_RO(g12a_cpu_clk_div16_en, HHI_SYS_CPU_CLK_CNTL1, 1, 0, { &g12a_cpu_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12a_cpu_clk_div16, 1, 16, { &g12a_cpu_clk_div16_en }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_apb_div, HHI_SYS_CPU_CLK_CNTL1, 3, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_apb, HHI_SYS_CPU_CLK_CNTL1, 1, 0, { &g12a_cpu_clk_apb_div }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_atb_div, HHI_SYS_CPU_CLK_CNTL1, 6, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_atb, HHI_SYS_CPU_CLK_CNTL1, 17, 0, { &g12a_cpu_clk_atb_div }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_axi_div, HHI_SYS_CPU_CLK_CNTL1, 9, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_axi, HHI_SYS_CPU_CLK_CNTL1, 18, 0, { &g12a_cpu_clk_axi_div }, 1, 0);
/* TODO: special case, ignore its parent clk at the moment */
static MESON_DIV_RO(g12a_cpu_clk_trace_div, HHI_SYS_CPU_CLK_CNTL1, 20, 3, CLK_DIVIDER_POWER_OF_TWO, { }, 0, 0);
static MESON_GATE_RO(g12a_cpu_clk_trace, HHI_SYS_CPU_CLK_CNTL1, 23, 0, { &g12a_cpu_clk_trace_div }, 1, 0);

static const struct reg_sequence g12a_hifi_init_regs[] = {
    { .reg = HHI_HIFI_PLL_CNTL1,    .def = 0x00000000 },
    { .reg = HHI_HIFI_PLL_CNTL2,    .def = 0x00000000 },
    { .reg = HHI_HIFI_PLL_CNTL3,    .def = 0x6a285c00 },
    { .reg = HHI_HIFI_PLL_CNTL4,    .def = 0x65771290 },
    { .reg = HHI_HIFI_PLL_CNTL5,    .def = 0x39272000 },
    { .reg = HHI_HIFI_PLL_CNTL6,    .def = 0x56540000 },
};

static struct clk g12a_hifi_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_HIFI_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_HIFI_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_HIFI_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .frac = {
            .reg_off = HHI_HIFI_PLL_CNTL1,
            .shift   = 0,
            .width   = 17,
        },
        .l = {
            .reg_off = HHI_HIFI_PLL_CNTL0,
            .shift   = 31,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_HIFI_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
        .range_min = 125,
        .range_max = 255,
        .init_regs = g12a_hifi_init_regs,
        .init_count = ARRAY_SIZE(g12a_hifi_init_regs),
        .flags = CLK_MESON_PLL_ROUND_CLOSEST,
    },
    .hw.init = &(struct clk_init_data){
        .name = "hifi_pll_dco",
        .ops = &meson_clk_pll_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
    },
};
static MESON_DIV(g12a_hifi_pll, HHI_HIFI_PLL_CNTL0, 16, 2, (CLK_DIVIDER_POWER_OF_TWO |
              CLK_DIVIDER_ROUND_CLOSEST), { &g12a_hifi_pll_dco }, 1, 0);

/*
 * The Meson G12A PCIE PLL is fined tuned to deliver a very precise
 * 100MHz reference clock for the PCIe Analog PHY, and thus requires
 * a strict register sequence to enable the PLL.
 */
static const struct reg_sequence g12a_pcie_pll_init_regs[] = {
    { .reg = HHI_PCIE_PLL_CNTL0,    .def = 0x20090496 },
    { .reg = HHI_PCIE_PLL_CNTL0,    .def = 0x30090496 },
    { .reg = HHI_PCIE_PLL_CNTL1,    .def = 0x00000000 },
    { .reg = HHI_PCIE_PLL_CNTL2,    .def = 0x00001100 },
    { .reg = HHI_PCIE_PLL_CNTL3,    .def = 0x10058e00 },
    { .reg = HHI_PCIE_PLL_CNTL4,    .def = 0x000100c0 },
    { .reg = HHI_PCIE_PLL_CNTL5,    .def = 0x68000048 },
    { .reg = HHI_PCIE_PLL_CNTL5,    .def = 0x68000068, .delay_us = 20 },
    { .reg = HHI_PCIE_PLL_CNTL4,    .def = 0x008100c0, .delay_us = 10 },
    { .reg = HHI_PCIE_PLL_CNTL0,    .def = 0x34090496 },
    { .reg = HHI_PCIE_PLL_CNTL0,    .def = 0x14090496, .delay_us = 10 },
    { .reg = HHI_PCIE_PLL_CNTL2,    .def = 0x00001000 },
};
/* Keep a single entry table for recalc/round_rate() ops */
static const struct pll_params_table g12a_pcie_pll_table[] = {
    { .m = 150, .n = 1 },
    { .m = 0, .n = 0},
};
static struct clk g12a_pcie_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_PCIE_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_PCIE_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_PCIE_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .frac = {
            .reg_off = HHI_PCIE_PLL_CNTL1,
            .shift   = 0,
            .width   = 12,
        },
        .l = {
            .reg_off = HHI_PCIE_PLL_CNTL0,
            .shift   = 31,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_PCIE_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
        .table = g12a_pcie_pll_table,
        .init_regs = g12a_pcie_pll_init_regs,
        .init_count = ARRAY_SIZE(g12a_pcie_pll_init_regs),
    },
    .hw.init = &(struct clk_init_data){
        .name = "pcie_pll_dco",
        .ops = &meson_clk_pcie_pll_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
    },
};
static MESON_FIXED_FACTOR(g12a_pcie_pll_dco_div2, 1, 2, { &g12a_pcie_pll_dco }, 1, 0);
static MESON_DIV(g12a_pcie_pll_od, HHI_PCIE_PLL_CNTL0, 16, 5, CLK_DIVIDER_ROUND_CLOSEST |
             CLK_DIVIDER_ONE_BASED |
             CLK_DIVIDER_ALLOW_ZERO, { &g12a_pcie_pll_dco_div2 }, 1, 0);
static MESON_FIXED_FACTOR(g12a_pcie_pll, 1, 2, { &g12a_pcie_pll_od }, 1, 0);
static struct clk g12a_hdmi_pll_dco = {
    .data = &(struct meson_clk_pll_data){
        .en = {
            .reg_off = HHI_HDMI_PLL_CNTL0,
            .shift   = 28,
            .width   = 1,
        },
        .m = {
            .reg_off = HHI_HDMI_PLL_CNTL0,
            .shift   = 0,
            .width   = 8,
        },
        .n = {
            .reg_off = HHI_HDMI_PLL_CNTL0,
            .shift   = 10,
            .width   = 5,
        },
        .frac = {
            .reg_off = HHI_HDMI_PLL_CNTL1,
            .shift   = 0,
            .width   = 16,
        },
        .l = {
            .reg_off = HHI_HDMI_PLL_CNTL0,
            .shift   = 30,
            .width   = 1,
        },
        .rst = {
            .reg_off = HHI_HDMI_PLL_CNTL0,
            .shift   = 29,
            .width   = 1,
        },
    },
    .hw.init = &(struct clk_init_data){
        .name = "hdmi_pll_dco",
        .ops = &meson_clk_pll_ro_ops,
        .parent_data = &(const struct clk_parent_data) {
            .fw_name = "xtal",
        },
        .num_parents = 1,
        /*
         * Display directly handle hdmi pll registers ATM, we need
         * NOCACHE to keep our view of the clock as accurate as possible
         */
        .flags = CLK_GET_RATE_NOCACHE,
    },
};
static MESON_DIV_RO(g12a_hdmi_pll_od, HHI_HDMI_PLL_CNTL0, 16, 2, CLK_DIVIDER_POWER_OF_TWO, { &g12a_hdmi_pll_dco }, 1, 0);
static MESON_DIV_RO(g12a_hdmi_pll_od2, HHI_HDMI_PLL_CNTL0, 18, 2, CLK_DIVIDER_POWER_OF_TWO, { &g12a_hdmi_pll_od }, 1, 0);
static MESON_DIV_RO(g12a_hdmi_pll, HHI_HDMI_PLL_CNTL0, 20, 2, CLK_DIVIDER_POWER_OF_TWO, { &g12a_hdmi_pll_od2 }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div4_div, 1, 4, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div4, HHI_FIX_PLL_CNTL1, 21, 0, { &g12a_fclk_div4_div }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div5_div, 1, 5, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div5, HHI_FIX_PLL_CNTL1, 22, 0, { &g12a_fclk_div5_div }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div7_div, 1, 7, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div7, HHI_FIX_PLL_CNTL1, 23, 0, { &g12a_fclk_div7_div }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div2p5_div, 1, 5, { &g12a_fixed_pll_dco }, 1, 0);
static MESON_GATE(g12a_fclk_div2p5, HHI_FIX_PLL_CNTL1, 25, 0, { &g12a_fclk_div2p5_div }, 1, 0);
static MESON_FIXED_FACTOR(g12a_mpll_50m_div, 1, 80, { &g12a_fixed_pll_dco }, 1, 0);
const static struct clk_parent_data g12a_mpll_50m_parent_table[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_mpll_50m_div },
};
static MESON_MUX_RO(g12a_mpll_50m, HHI_FIX_PLL_CNTL3, 0x1, 5, 0, 0, g12a_mpll_50m_parent_table, 2, 0);
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
        /* .lock = &meson_clk_lock, */
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
static MESON_GATE(g12a_mpll0, HHI_MPLL_CNTL1, 31, 0, { &g12a_mpll0_div }, 1, 0);
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
        /* .lock = &meson_clk_lock, */
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
static MESON_GATE(g12a_mpll1, HHI_MPLL_CNTL3, 31, 0, { &g12a_mpll1_div }, 1, 0);
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
        /* .lock = &meson_clk_lock, */
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
static MESON_GATE(g12a_mpll2, HHI_MPLL_CNTL5, 31, 0, { &g12a_mpll2_div }, 1, 0);
static const struct reg_sequence g12a_mpll3_init_regs[] = {
    { .reg = HHI_MPLL_CNTL8,    .def = 0x40000033 },
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
            .width     = 1,
        },
        .n2 = {
            .reg_off = HHI_MPLL_CNTL7,
            .shift   = 20,
            .width   = 9,
        },
        .ssen = {
            .reg_off = HHI_MPLL_CNTL7,
            .shift   = 29,
            .width     = 1,
        },
        /* .lock = &meson_clk_lock, */
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
static MESON_GATE(g12a_mpll3, HHI_MPLL_CNTL7, 31, 0, { &g12a_mpll3_div }, 1, 0);

static uint32_t mux_table_clk81[] = { 0, 2, 3, 4, 5, 6, 7 };
static const struct clk_parent_data clk81_parent_data[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div7 },
    { .clk = &g12a_mpll1 },
    { .clk = &g12a_mpll2 },
    { .clk = &g12a_fclk_div4 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &g12a_fclk_div5 },
};
static MESON_MUX_RO(g12a_mpeg_clk_sel, HHI_MPEG_CLK_CNTL, 0x7, 12, mux_table_clk81, 0, clk81_parent_data, ARRAY_SIZE(clk81_parent_data), 0);
static MESON_DIV(g12a_mpeg_clk_div, HHI_MPEG_CLK_CNTL, 0, 7, 0, { &g12a_mpeg_clk_sel }, 1, 0);
static MESON_GATE(g12a_clk81, HHI_MPEG_CLK_CNTL, 7, 0, { &g12a_mpeg_clk_div }, 1, 0);
static const struct clk_parent_data g12a_sd_emmc_clk0_parent_data[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div2 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &g12a_fclk_div5 },
    { .clk = &g12a_fclk_div7 },
};
static MESON_MUX(g12a_sd_emmc_a_clk0_sel, HHI_SD_EMMC_CLK_CNTL, 0x7, 9, 0, 0, g12a_sd_emmc_clk0_parent_data, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_sd_emmc_a_clk0_div, HHI_SD_EMMC_CLK_CNTL, 0, 7, 0, { &g12a_sd_emmc_a_clk0_sel }, 1, 0);
static MESON_GATE(g12a_sd_emmc_a_clk0, HHI_SD_EMMC_CLK_CNTL, 7, 0, { &g12a_sd_emmc_a_clk0_div }, 1, 0);
static MESON_MUX(g12a_sd_emmc_b_clk0_sel, HHI_SD_EMMC_CLK_CNTL, 0x7, 25, 0, 0, g12a_sd_emmc_clk0_parent_data, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_sd_emmc_b_clk0_div, HHI_SD_EMMC_CLK_CNTL, 16, 7, 0, { &g12a_sd_emmc_b_clk0_sel }, 1, 0);
static MESON_GATE(g12a_sd_emmc_b_clk0, HHI_SD_EMMC_CLK_CNTL, 23, 0, { &g12a_sd_emmc_b_clk0_div }, 1, 0);
static MESON_MUX(g12a_sd_emmc_c_clk0_sel, HHI_NAND_CLK_CNTL, 0x7, 9, 0, 0, g12a_sd_emmc_clk0_parent_data, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_sd_emmc_c_clk0_div, HHI_NAND_CLK_CNTL, 0, 7, 0, { &g12a_sd_emmc_c_clk0_sel }, 1, 0);
static MESON_GATE(g12a_sd_emmc_c_clk0, HHI_NAND_CLK_CNTL, 7, 0, { &g12a_sd_emmc_c_clk0_div }, 1, 0);
static struct clk g12a_vid_pll_div = {
    .data = &(struct meson_vid_pll_div_data){
        .val = {
            .reg_off = HHI_VID_PLL_CLK_DIV,
            .shift   = 0,
            .width   = 15,
        },
        .sel = {
            .reg_off = HHI_VID_PLL_CLK_DIV,
            .shift   = 16,
            .width   = 2,
        },
    },
    .hw.init = &(struct clk_init_data) {
        .name = "vid_pll_div",
        .ops = &meson_vid_pll_div_ro_ops,
        .parent_clks = (const struct clk *[]) { &g12a_hdmi_pll },
        .num_parents = 1,
        .flags = CLK_SET_RATE_PARENT | CLK_GET_RATE_NOCACHE,
    },
};
static const struct clk_parent_data g12a_vid_pll_parent_table[] = {
    { .clk = &g12a_vid_pll_div, },
    { .clk = &g12a_hdmi_pll, },
};

static MESON_MUX(g12a_vid_pll_sel, HHI_VID_PLL_CLK_DIV, 0x1, 18, 0, 0, g12a_vid_pll_parent_table, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_GATE(g12a_vid_pll, HHI_VID_PLL_CLK_DIV, 19, 0, { &g12a_vid_pll_sel }, 1, 0);
const static struct clk_parent_data g12a_vpu_sel_parent_table[] = {
    { .clk = &g12a_fclk_div3, },
    { .clk = &g12a_fclk_div4, },
    { .clk = &g12a_fclk_div5, },
    { .clk = &g12a_fclk_div7, },
    { .clk = &g12a_mpll1, },
    { .clk = &g12a_vid_pll, },
    { .clk = &g12a_hifi_pll, },
    { .clk = &g12a_gp0_pll, },
};
static MESON_MUX(g12a_vpu_0_sel, HHI_VPU_CLK_CNTL, 0x7, 9, 0, 0, g12a_vpu_sel_parent_table, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vpu_0_div, HHI_VPU_CLK_CNTL, 0, 7, 0, { &g12a_vpu_0_sel }, 1, 0);
static MESON_GATE(g12a_vpu_0, HHI_VPU_CLK_CNTL, 8, 0, { &g12a_vpu_0_div }, 1, 0);
static MESON_MUX(g12a_vpu_1_sel, HHI_VPU_CLK_CNTL, 0x7, 25, 0, 0, g12a_vpu_sel_parent_table, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vpu_1_div, HHI_VPU_CLK_CNTL, 16, 7, 0, { &g12a_vpu_1_sel }, 1, 0);
static MESON_GATE(g12a_vpu_1, HHI_VPU_CLK_CNTL, 24, 0, { &g12a_vpu_1_div }, 1, 0);
const struct clk_parent_data g12a_vpu_parent_table[] = {
    { .clk = &g12a_vpu_0 },
    { .clk = &g12a_vpu_1 },
};
static MESON_MUX(g12a_vpu, HHI_VPU_CLK_CNTL, 1, 31, 0, 0, g12a_vpu_parent_table, 2, 0);
static const struct clk_parent_data g12a_vdec_parent_table[] = {
    { .clk = &g12a_fclk_div2p5, },
    { .clk = &g12a_fclk_div3, },
    { .clk = &g12a_fclk_div4, },
    { .clk = &g12a_fclk_div5, },
    { .clk = &g12a_fclk_div7, },
    { .clk = &g12a_hifi_pll, },
    { .clk = &g12a_gp0_pll, },
};

static MESON_MUX(g12a_vdec_1_sel, HHI_VDEC_CLK_CNTL, 0x7, 9, 0, CLK_MUX_ROUND_CLOSEST, g12a_vdec_parent_table, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_vdec_1_div, HHI_VDEC_CLK_CNTL, 0, 7, CLK_DIVIDER_ROUND_CLOSEST, { &g12a_vdec_1_sel }, 1, 0);
static MESON_GATE(g12a_vdec_1, HHI_VDEC_CLK_CNTL, 8, 0, { &g12a_vdec_1_div }, 1, 0);
static MESON_MUX(g12a_vdec_hevcf_sel, HHI_VDEC2_CLK_CNTL, 0x7, 9, 0, CLK_MUX_ROUND_CLOSEST, g12a_vdec_parent_table, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_vdec_hevcf_div, HHI_VDEC2_CLK_CNTL, 0, 7, CLK_DIVIDER_ROUND_CLOSEST, { &g12a_vdec_hevcf_sel }, 1, 0);
static MESON_GATE(g12a_vdec_hevcf, HHI_VDEC2_CLK_CNTL, 8, 0, { &g12a_vdec_hevcf_div }, 1, 0);
static MESON_MUX(g12a_vdec_hevc_sel, HHI_VDEC2_CLK_CNTL, 0x7, 25, 0, CLK_MUX_ROUND_CLOSEST, g12a_vdec_parent_table, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_vdec_hevc_div, HHI_VDEC2_CLK_CNTL, 16, 7, CLK_DIVIDER_ROUND_CLOSEST, { &g12a_vdec_hevc_sel }, 1, 0);
static MESON_GATE(g12a_vdec_hevc, HHI_VDEC2_CLK_CNTL, 24, 0, { &g12a_vdec_hevc_div }, 1, 0);
static const struct clk_parent_data g12a_vapb_parent_table[] = {
    { .clk = &g12a_fclk_div4, },
    { .clk = &g12a_fclk_div3, },
    { .clk = &g12a_fclk_div5, },
    { .clk = &g12a_fclk_div7, },
    { .clk = &g12a_mpll1, },
    { .clk = &g12a_vid_pll, },
    { .clk = &g12a_mpll2, },
    { .clk = &g12a_fclk_div2p5, },
};
static MESON_MUX(g12a_vapb_0_sel, HHI_VAPBCLK_CNTL, 0x3, 9, 0, 0, g12a_vapb_parent_table, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vapb_0_div, HHI_VAPBCLK_CNTL, 0, 7, 0, { &g12a_vapb_0_sel }, 1, 0);
static MESON_GATE(g12a_vapb_0, HHI_VAPBCLK_CNTL, 8, 0, { &g12a_vapb_0_div }, 1, 0);
static MESON_MUX(g12a_vapb_1_sel, HHI_VAPBCLK_CNTL, 0x3, 25, 0, 0, g12a_vapb_parent_table, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vapb_1_div, HHI_VAPBCLK_CNTL, 16, 7, 0, { &g12a_vapb_1_sel }, 1, 0);
static MESON_GATE(g12a_vapb_1, HHI_VAPBCLK_CNTL, 24, 0, { &g12a_vapb_1_div }, 1, 0);
const struct clk_parent_data g12a_vapb_sel_parent_table[] = {
    { .clk = &g12a_vapb_0 },
    { .clk = &g12a_vapb_1 },
};
static MESON_MUX(g12a_vapb_sel, HHI_VAPBCLK_CNTL, 1, 31, 0, 0, g12a_vapb_sel_parent_table, 2, 0);
static MESON_GATE(g12a_vapb, HHI_VAPBCLK_CNTL, 30, 0, { &g12a_vapb_sel }, 1, 0);
static const struct clk_parent_data g12a_vclk_parent_table[] = {
    { .clk = &g12a_vid_pll, },
    { .clk = &g12a_gp0_pll, },
    { .clk = &g12a_hifi_pll, },
    { .clk = &g12a_mpll1, },
    { .clk = &g12a_fclk_div3, },
    { .clk = &g12a_fclk_div4, },
    { .clk = &g12a_fclk_div5, },
    { .clk = &g12a_fclk_div7, },
};
static MESON_MUX(g12a_vclk_sel, HHI_VID_CLK_CNTL, 0x7, 16, 0, 0, g12a_vclk_parent_table, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_vclk2_sel, HHI_VIID_CLK_CNTL, 0x7, 16, 0, 0, g12a_vclk_parent_table, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_GATE(g12a_vclk_input, HHI_VID_CLK_DIV, 16, 0, { &g12a_vclk_sel }, 1, 0);
static MESON_GATE(g12a_vclk2_input, HHI_VIID_CLK_DIV, 16, 0, { &g12a_vclk2_sel }, 1, 0);
static MESON_DIV(g12a_vclk_div, HHI_VID_CLK_DIV, 0, 8, 0, { &g12a_vclk_input }, 1, 0);
static struct clk g12a_vclk2_div = {
    .data = &(struct meson_vclk_div_data){
        .div = {
            .reg_off = HHI_VIID_CLK_DIV,
            .shift   = 0,
            .width   = 8,
        },
        .enable = {
            .reg_off = HHI_VIID_CLK_DIV,
            .shift   = 16,
            .width   = 1,
        },
        .reset = {
            .reg_off = HHI_VIID_CLK_DIV,
            .shift   = 17,
            .width   = 1,
        },
        .flags = CLK_DIVIDER_ROUND_CLOSEST,
    },
    .hw.init = &(struct clk_init_data){
        .name = "vclk2_div",
        .ops = &meson_vclk_div_ops,
        .parent_clks = (const struct clk *[]) {
            &g12a_vclk2_input
        },
        .num_parents = 1,
        .flags = CLK_SET_RATE_GATE,
    },
};
static MESON_GATE(g12a_vclk, HHI_VID_CLK_CNTL, 19, 0, { &g12a_vclk_div }, 1, 0);
static struct clk g12a_vclk2 = {
    .data = &(struct meson_vclk_gate_data){
        .enable = {
            .reg_off = HHI_VIID_CLK_CNTL,
            .shift   = 19,
            .width   = 1,
        },
        .reset = {
            .reg_off = HHI_VIID_CLK_CNTL,
            .shift   = 15,
            .width   = 1,
        },
    },
    .hw.init = &(struct clk_init_data) {
        .name = "vclk2",
        .ops = &meson_vclk_gate_ops,
        .parent_clks = (const struct clk *[]) { &g12a_vclk2_div },
        .num_parents = 1,
        .flags = CLK_SET_RATE_PARENT,
    },
};
static MESON_GATE(g12a_vclk_div1, HHI_VID_CLK_CNTL, 0, 0, { &g12a_vclk }, 1, 0);
static MESON_GATE(g12a_vclk_div2_en, HHI_VID_CLK_CNTL, 1, 0, { &g12a_vclk }, 1, 0);
static MESON_GATE(g12a_vclk_div4_en, HHI_VID_CLK_CNTL, 2, 0, { &g12a_vclk }, 1, 0);
static MESON_GATE(g12a_vclk_div6_en, HHI_VID_CLK_CNTL, 3, 0, { &g12a_vclk }, 1, 0);
static MESON_GATE(g12a_vclk_div12_en, HHI_VID_CLK_CNTL, 4, 0, { &g12a_vclk }, 1, 0);
static MESON_GATE(g12a_vclk2_div1, HHI_VIID_CLK_CNTL, 0, 0, { &g12a_vclk2 }, 1, 0);
static MESON_GATE(g12a_vclk2_div2_en, HHI_VIID_CLK_CNTL, 1, 0, { &g12a_vclk2 }, 1, 0);
static MESON_GATE(g12a_vclk2_div4_en, HHI_VIID_CLK_CNTL, 2, 0, { &g12a_vclk2 }, 1, 0);
static MESON_GATE(g12a_vclk2_div6_en, HHI_VIID_CLK_CNTL, 3, 0, { &g12a_vclk2 }, 1, 0);
static MESON_GATE(g12a_vclk2_div12_en, HHI_VIID_CLK_CNTL, 4, 0, { &g12a_vclk2 }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk_div2, 1, 2, { &g12a_vclk_div2_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk_div4, 1, 4, { &g12a_vclk_div4_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk_div6, 1, 6, { &g12a_vclk_div6_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk_div12, 1, 12, { &g12a_vclk_div12_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk2_div2, 1, 2, { &g12a_vclk2_div2_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk2_div4, 1, 4, { &g12a_vclk2_div4_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk2_div6, 1, 6, { &g12a_vclk2_div6_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_vclk2_div12, 1, 12, { &g12a_vclk2_div12_en }, 1, 0);
static uint32_t mux_table_cts_sel[] = { 0, 1, 2, 3, 4, 8, 9, 10, 11, 12 };
static const struct clk_parent_data g12a_cts_parent_table[] = {
    { .clk = &g12a_vclk_div1, },
    { .clk = &g12a_vclk_div2, },
    { .clk = &g12a_vclk_div4, },
    { .clk = &g12a_vclk_div6, },
    { .clk = &g12a_vclk_div12, },
    { .clk = &g12a_vclk2_div1, },
    { .clk = &g12a_vclk2_div2, },
    { .clk = &g12a_vclk2_div4, },
    { .clk = &g12a_vclk2_div6, },
    { .clk = &g12a_vclk2_div12, },
};
static MESON_MUX(g12a_cts_enci_sel, HHI_VID_CLK_DIV, 0xf, 28, mux_table_cts_sel, 0, g12a_cts_parent_table, ARRAY_SIZE(g12a_cts_parent_table), CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_cts_encp_sel, HHI_VID_CLK_DIV, 0xf, 20, mux_table_cts_sel, 0, g12a_cts_parent_table, ARRAY_SIZE(g12a_cts_parent_table), CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_cts_encl_sel, HHI_VIID_CLK_DIV, 0xf, 12, mux_table_cts_sel, 0, g12a_cts_parent_table, ARRAY_SIZE(g12a_cts_parent_table), CLK_SET_RATE_PARENT | CLK_SET_RATE_NO_REPARENT);
static MESON_MUX(g12a_cts_vdac_sel, HHI_VIID_CLK_DIV, 0xf, 28, mux_table_cts_sel, 0, g12a_cts_parent_table, ARRAY_SIZE(g12a_cts_parent_table), CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static uint32_t mux_table_hdmi_tx_sel[] = { 0, 1, 2, 3, 4, 8, 9, 10, 11, 12 };
static const struct clk_parent_data g12a_cts_hdmi_tx_parent_table[] = {
    { .clk = &g12a_vclk_div1, },
    { .clk = &g12a_vclk_div2, },
    { .clk = &g12a_vclk_div4, },
    { .clk = &g12a_vclk_div6, },
    { .clk = &g12a_vclk_div12, },
    { .clk = &g12a_vclk2_div1, },
    { .clk = &g12a_vclk2_div2, },
    { .clk = &g12a_vclk2_div4, },
    { .clk = &g12a_vclk2_div6, },
    { .clk = &g12a_vclk2_div12, },
};
static MESON_MUX(g12a_hdmi_tx_sel, HHI_HDMI_CLK_CNTL, 0xf, 16, mux_table_hdmi_tx_sel, 0, g12a_cts_hdmi_tx_parent_table, ARRAY_SIZE(g12a_cts_hdmi_tx_parent_table), CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_GATE(g12a_cts_enci, HHI_VID_CLK_CNTL2, 0, 0, { &g12a_cts_enci_sel }, 1, 0);
static MESON_GATE(g12a_cts_encp, HHI_VID_CLK_CNTL2, 2, 0, { &g12a_cts_encp_sel }, 1, 0);
static MESON_GATE(g12a_cts_encl, HHI_VID_CLK_CNTL2, 3, 0, { &g12a_cts_encl_sel }, 1, 0);
static MESON_GATE(g12a_cts_vdac, HHI_VID_CLK_CNTL2, 4, 0, { &g12a_cts_vdac_sel }, 1, 0);
static MESON_GATE(g12a_hdmi_tx, HHI_VID_CLK_CNTL2, 5, 0, { &g12a_hdmi_tx_sel }, 1, 0);
static const struct clk_parent_data g12a_mipi_dsi_pxclk_parent_table[] = {
    { .clk = &g12a_vid_pll, },
    { .clk = &g12a_gp0_pll, },
    { .clk = &g12a_hifi_pll, },
    { .clk = &g12a_mpll1, },
    { .clk = &g12a_fclk_div2, },
    { .clk = &g12a_fclk_div2p5, },
    { .clk = &g12a_fclk_div3, },
    { .clk = &g12a_fclk_div7, },
};
static MESON_MUX(g12a_mipi_dsi_pxclk_sel, HHI_MIPIDSI_PHY_CLK_CNTL, 0x7, 12, 0, CLK_MUX_ROUND_CLOSEST, g12a_mipi_dsi_pxclk_parent_table, ARRAY_SIZE(g12a_mipi_dsi_pxclk_parent_table), CLK_SET_RATE_NO_REPARENT | CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_mipi_dsi_pxclk_div, HHI_MIPIDSI_PHY_CLK_CNTL, 0, 7, 0, { &g12a_mipi_dsi_pxclk_sel }, 1, 0);
static MESON_GATE(g12a_mipi_dsi_pxclk, HHI_MIPIDSI_PHY_CLK_CNTL, 8, 0, { &g12a_mipi_dsi_pxclk_div }, 1, 0);
static const struct clk_parent_data g12a_hdmi_parent_table[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_fclk_div4 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &g12a_fclk_div5 },
};
static MESON_MUX(g12a_hdmi_sel, HHI_HDMI_CLK_CNTL, 0x3, 9, 0, CLK_MUX_ROUND_CLOSEST, g12a_hdmi_parent_table, ARRAY_SIZE(g12a_hdmi_parent_table), CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_DIV(g12a_hdmi_div, HHI_HDMI_CLK_CNTL, 0, 7, 0, { &g12a_hdmi_sel }, 1, 0);
static MESON_GATE(g12a_hdmi, HHI_HDMI_CLK_CNTL, 8, 0, { &g12a_hdmi_div }, 1, 0);
static const struct clk_parent_data g12a_mali_0_1_parent_data[] = {
    { .fw_name = "xtal", },
    { .clk = &g12a_gp0_pll },
    { .clk = &g12a_hifi_pll },
    { .clk = &g12a_fclk_div2p5 },
    { .clk = &g12a_fclk_div3 },
    { .clk = &g12a_fclk_div4 },
    { .clk = &g12a_fclk_div5 },
    { .clk = &g12a_fclk_div7 },
};
static MESON_MUX(g12a_mali_0_sel, HHI_MALI_CLK_CNTL, 0x7, 9, 0, 0, g12a_mali_0_1_parent_data, 8, 0);
static MESON_DIV(g12a_mali_0_div, HHI_MALI_CLK_CNTL, 0, 7, 0, { &g12a_mali_0_sel }, 1, 0);
static MESON_GATE(g12a_mali_0, HHI_MALI_CLK_CNTL, 8, 0, { &g12a_mali_0_div }, 1, 0);
static MESON_MUX(g12a_mali_1_sel, HHI_MALI_CLK_CNTL, 0x7, 25, 0, 0, g12a_mali_0_1_parent_data, 8, 0);
static MESON_DIV(g12a_mali_1_div, HHI_MALI_CLK_CNTL, 16, 7, 0, { &g12a_mali_1_sel }, 1, 0);
static MESON_GATE(g12a_mali_1, HHI_MALI_CLK_CNTL, 24, 0, { &g12a_mali_1_div }, 1, 0);
static const struct clk_parent_data g12a_mali_parent_table[] = {
    { .clk = &g12a_mali_0, },
    { .clk = &g12a_mali_1, },
};
static MESON_MUX(g12a_mali, HHI_MALI_CLK_CNTL, 1, 31, 0, 0, g12a_mali_parent_table, 2, CLK_SET_RATE_PARENT);
static MESON_DIV_RO(g12a_ts_div, HHI_TS_CLK_CNTL, 0, 8, 0, { &g12a_ts_div }, 1, 0);
static MESON_GATE(g12a_ts, HHI_TS_CLK_CNTL, 8, 0, { &g12a_ts_div }, 1, 0);
static const struct clk_parent_data spicc_sclk_parent_data[] = {
	{ .fw_name = "xtal", },
	{ .clk = &g12a_clk81 },
	{ .clk = &g12a_fclk_div4 },
	{ .clk = &g12a_fclk_div3 },
	{ .clk = &g12a_fclk_div5 },
	{ .clk = &g12a_fclk_div7 },
};

static MESON_MUX(g12a_spicc0_sclk_sel, HHI_SPICC_CLK_CNTL, 7, 7, 0, 0, spicc_sclk_parent_data, 0, 0);
static MESON_DIV(g12a_spicc0_sclk_div, HHI_SPICC_CLK_CNTL, 0, 6, 0, { &g12a_spicc0_sclk_sel }, 1, 0);
static MESON_GATE(g12a_spicc0_sclk, HHI_SPICC_CLK_CNTL, 6, 0, { &g12a_spicc0_sclk_div }, 1, 0);
static MESON_MUX(g12a_spicc1_sclk_sel, HHI_SPICC_CLK_CNTL, 7, 23, 0, 0, spicc_sclk_parent_data, 0, 0);
static MESON_DIV(g12a_spicc1_sclk_div, HHI_SPICC_CLK_CNTL, 16, 6, 0, { &g12a_spicc1_sclk_sel }, 1, 0);
static MESON_GATE(g12a_spicc1_sclk, HHI_SPICC_CLK_CNTL, 22, 0, { &g12a_spicc1_sclk_div }, 1, 0);
static const struct clk_parent_data nna_clk_parent_data[] = {
	{ .fw_name = "xtal", },
	{ .clk = &g12a_gp0_pll, },
	{ .clk = &g12a_hifi_pll, },
	{ .clk = &g12a_fclk_div2p5, },
	{ .clk = &g12a_fclk_div3, },
	{ .clk = &g12a_fclk_div4, },
	{ .clk = &g12a_fclk_div5, },
	{ .clk = &g12a_fclk_div7 },
};
static MESON_MUX(sm1_nna_axi_clk_sel, HHI_NNA_CLK_CNTL, 7, 9, 0, 0, nna_clk_parent_data, 0, 0);
static MESON_DIV(sm1_nna_axi_clk_div, HHI_NNA_CLK_CNTL, 0, 7, 0, { &sm1_nna_axi_clk_sel }, 1, 0);
static MESON_GATE(sm1_nna_axi_clk, HHI_NNA_CLK_CNTL, 8, 0, { &sm1_nna_axi_clk_div }, 1, 0);
static MESON_MUX(sm1_nna_core_clk_sel, HHI_NNA_CLK_CNTL, 7, 25, 0, 0, nna_clk_parent_data, 0, 0);
static MESON_DIV(sm1_nna_core_clk_div, HHI_NNA_CLK_CNTL, 16, 7, 0, { &sm1_nna_core_clk_sel }, 1, 0);
static MESON_GATE(sm1_nna_core_clk, HHI_NNA_CLK_CNTL, 24, 0, { &sm1_nna_core_clk_div }, 1, 0);

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
static MESON_CLK81_GATE(g12a_mmc_pclk,        HHI_GCLK_MPEG2,    11);
static MESON_CLK81_GATE(g12a_uart2,            HHI_GCLK_MPEG2,    15);
static MESON_CLK81_GATE(g12a_vpu_intr,        HHI_GCLK_MPEG2,    25);
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
    [CLKID_SYS_PLL]            = &g12a_sys_pll,
    [CLKID_FIXED_PLL]        = &g12a_fixed_pll,
    [CLKID_FCLK_DIV2]        = &g12a_fclk_div2,
    [CLKID_FCLK_DIV3]        = &g12a_fclk_div3,
    [CLKID_FCLK_DIV4]        = &g12a_fclk_div4,
    [CLKID_FCLK_DIV5]        = &g12a_fclk_div5,
    [CLKID_FCLK_DIV7]        = &g12a_fclk_div7,
    [CLKID_FCLK_DIV2P5]        = &g12a_fclk_div2p5,
    [CLKID_GP0_PLL]            = &g12a_gp0_pll,
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
    [CLKID_SD_EMMC_B_CLK0_SEL]    = &g12a_sd_emmc_b_clk0_sel,
    [CLKID_SD_EMMC_B_CLK0_DIV]    = &g12a_sd_emmc_b_clk0_div,
    [CLKID_SD_EMMC_B_CLK0]        = &g12a_sd_emmc_b_clk0,
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
    [CLKID_FCLK_DIV2P5_DIV]        = &g12a_fclk_div2p5_div,
    [CLKID_HIFI_PLL]        = &g12a_hifi_pll,
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
    [CLKID_SYS_PLL_DCO]        = &g12a_sys_pll_dco,
    [CLKID_GP0_PLL_DCO]        = &g12a_gp0_pll_dco,
    [CLKID_HIFI_PLL_DCO]        = &g12a_hifi_pll_dco,
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
    [CLKID_HDMI_PLL_DCO]        = &g12a_hdmi_pll_dco,
    [CLKID_HDMI_PLL_OD]        = &g12a_hdmi_pll_od,
    [CLKID_HDMI_PLL_OD2]        = &g12a_hdmi_pll_od2,
    [CLKID_HDMI_PLL]        = &g12a_hdmi_pll,
    /* [CLKID_VID_PLL]            = &g12a_vid_pll_div, */
    /* [CLKID_VID_PLL_SEL]        = &g12a_vid_pll_sel, */
    /* [CLKID_VID_PLL_DIV]        = &g12a_vid_pll, */
    [CLKID_VCLK_SEL]        = &g12a_vclk_sel,
    [CLKID_VCLK2_SEL]        = &g12a_vclk2_sel,
    [CLKID_VCLK_INPUT]        = &g12a_vclk_input,
    [CLKID_VCLK2_INPUT]        = &g12a_vclk2_input,
    [CLKID_VCLK_DIV]        = &g12a_vclk_div,
    [CLKID_VCLK2_DIV]        = &g12a_vclk2_div,
    [CLKID_VCLK]            = &g12a_vclk,
    [CLKID_VCLK2]            = &g12a_vclk2,
    [CLKID_VCLK_DIV1]        = &g12a_vclk_div1,
    [CLKID_VCLK_DIV2_EN]        = &g12a_vclk_div2_en,
    [CLKID_VCLK_DIV4_EN]        = &g12a_vclk_div4_en,
    [CLKID_VCLK_DIV6_EN]        = &g12a_vclk_div6_en,
    [CLKID_VCLK_DIV12_EN]        = &g12a_vclk_div12_en,
    [CLKID_VCLK2_DIV1]        = &g12a_vclk2_div1,
    [CLKID_VCLK2_DIV2_EN]        = &g12a_vclk2_div2_en,
    [CLKID_VCLK2_DIV4_EN]        = &g12a_vclk2_div4_en,
    [CLKID_VCLK2_DIV6_EN]        = &g12a_vclk2_div6_en,
    [CLKID_VCLK2_DIV12_EN]        = &g12a_vclk2_div12_en,
    [CLKID_VCLK_DIV2]        = &g12a_vclk_div2,
    [CLKID_VCLK_DIV4]        = &g12a_vclk_div4,
    [CLKID_VCLK_DIV6]        = &g12a_vclk_div6,
    [CLKID_VCLK_DIV12]        = &g12a_vclk_div12,
    [CLKID_VCLK2_DIV2]        = &g12a_vclk2_div2,
    [CLKID_VCLK2_DIV4]        = &g12a_vclk2_div4,
    [CLKID_VCLK2_DIV6]        = &g12a_vclk2_div6,
    [CLKID_VCLK2_DIV12]        = &g12a_vclk2_div12,
    /* [CLKID_CTS_ENCI_SEL]        = &g12a_cts_enci_sel, */
    /* [CLKID_CTS_ENCP_SEL]        = &g12a_cts_encp_sel, */
    /* [CLKID_CTS_ENCL_SEL]        = &g12a_cts_encl_sel, */
    /* [CLKID_CTS_VDAC_SEL]        = &g12a_cts_vdac_sel, */
    [CLKID_HDMI_TX_SEL]        = &g12a_hdmi_tx_sel,
    /* [CLKID_CTS_ENCI]        = &g12a_cts_enci, */
    /* [CLKID_CTS_ENCP]        = &g12a_cts_encp, */
    /* [CLKID_CTS_ENCL]        = &g12a_cts_encl, */
    /* [CLKID_CTS_VDAC]        = &g12a_cts_vdac, */
    [CLKID_HDMI_TX]            = &g12a_hdmi_tx,
    [CLKID_HDMI_SEL]        = &g12a_hdmi_sel,
    [CLKID_HDMI_DIV]        = &g12a_hdmi_div,
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
    [CLKID_PCIE_PLL_DCO]        = &g12a_pcie_pll_dco,
    [CLKID_PCIE_PLL_DCO_DIV2]    = &g12a_pcie_pll_dco_div2,
    [CLKID_PCIE_PLL_OD]        = &g12a_pcie_pll_od,
    [CLKID_PCIE_PLL]        = &g12a_pcie_pll,
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
    [CLKID_GP1_PLL_DCO]        = &sm1_gp1_pll_dco,
    [CLKID_GP1_PLL]            = &sm1_gp1_pll,
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

struct clk **get_clk_list(void)
{
    return sm1_clks;
}
