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
	.init = &(struct clk_init_data){
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
		.range = &g12a_sys_pll_mult_range,
	},
	.init = &(struct clk_init_data){
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
static struct clk g12b_sys1_pll_dco = { 
	.data = &(struct meson_clk_pll_data){
		.en = {
			.reg_off = HHI_SYS1_PLL_CNTL0,
			.shift   = 28,
			.width   = 1,
		},
		.m = {
			.reg_off = HHI_SYS1_PLL_CNTL0,
			.shift   = 0,
			.width   = 8,
		},
		.n = {
			.reg_off = HHI_SYS1_PLL_CNTL0,
			.shift   = 10,
			.width   = 5,
		},
		.l = {
			.reg_off = HHI_SYS1_PLL_CNTL0,
			.shift   = 31,
			.width   = 1,
		},
		.rst = {
			.reg_off = HHI_SYS1_PLL_CNTL0,
			.shift   = 29,
			.width   = 1,
		},
		.range = &g12a_sys_pll_mult_range,
	},
	.init = &(struct clk_init_data){
		.name = "sys1_pll_dco",
		.ops = &meson_clk_pll_ops,
		.parent_data = &(const struct clk_parent_data) {
			.fw_name = "xtal",
		},
		.num_parents = 1,
		/* This clock feeds the CPU, avoid disabling it */
		.flags = CLK_IS_CRITICAL,
	},
};
static MESON_DIV(g12b_sys1_pll, HHI_SYS1_PLL_CNTL0, 16, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12b_sys1_pll_dco }, 1, 0);
static MESON_GATE_RO(g12a_sys_pll_div16_en, HHI_SYS_CPU_CLK_CNTL1, 24, 0, { &g12a_sys_pll }, 1, 0);
static MESON_GATE_RO(g12b_sys1_pll_div16_en, HHI_SYS_CPUB_CLK_CNTL1, 24, 0, { &g12b_sys1_pll }, 1, 0);
static MESON_FIXED_FACTOR(g12a_sys_pll_div16, 1, 16, { &g12a_sys_pll_div16_en }, 1, 0);
static MESON_FIXED_FACTOR(g12b_sys1_pll_div16, 1, 16, { &g12b_sys1_pll_div16_en }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div2_div, 1, 2, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div2, HHI_FIX_PLL_CNTL1, 24, 0, { &g12a_fclk_div2_div }, 1, 0);
static MESON_FIXED_FACTOR(g12a_fclk_div3_div, 1, 3, { &g12a_fixed_pll }, 1, 0);
static MESON_GATE(g12a_fclk_div3, HHI_FIX_PLL_CNTL1, 20, 0, { &g12a_fclk_div3_div }, 1, 0);
static MESON_MUX(g12a_cpu_clk_premux0, HHI_SYS_CPU_CLK_CNTL0, 0x3, 0, NULL, CLK_MUX_ROUND_CLOSEST, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_fclk_div2.hw },
			{ .hw = &g12a_fclk_div3.hw },
		}, 3, 0);
static MESON_MUX(g12a_cpu_clk_premux1, HHI_SYS_CPU_CLK_CNTL0, 0x3, 16, NULL, 0, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_fclk_div2.hw },
			{ .hw = &g12a_fclk_div3.hw },
		}, 3, 0);
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
	.init = &(struct clk_init_data){
		.name = "cpu_clk_dyn0_div",
		.ops = &meson_clk_cpu_dyndiv_ops,
		.parent_clks = (const struct clk *[]) {
			&g12a_cpu_clk_premux0
		},
		.num_parents = 1,
		.flags = CLK_SET_RATE_PARENT,
	},
};
const struct clk_parent_data [] g12a_cpu_clk_postmux0_parent_table = {
    { .clk = &g12a_cpu_clk_premux0 }, 
    { .clk = &g12a_cpu_clk_mux0_div }, 
};
static MESON_MUX(g12a_cpu_clk_postmux0, HHI_SYS_CPU_CLK_CNTL0, 0x1, 2, NULL, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_postmux0_parent_table, 2, 0);
static MESON_DIV_RO(g12a_cpu_clk_mux1_div, HHI_SYS_CPU_CLK_CNTL0, 20, 6, 0, { &g12a_cpu_clk_premux1 }, 1, 0);
const struct clk_parent_data [] g12a_cpu_clk_postmux1_parent_table = {
    { .clk = &g12a_cpu_clk_premux1 }, 
    { .clk = &g12a_cpu_clk_mux1_div }, 
};
static MESON_MUX(g12a_cpu_clk_postmux1, HHI_SYS_CPU_CLK_CNTL0, 0x1, 18, NULL, 0, g12a_cpu_clk_postmux1_parent_table, 2, 0);
const struct clk_parent_data [] g12a_cpu_clk_dyn_parent_table = {
    { .clk = &g12a_cpu_clk_postmux0 }, 
    { .clk = &g12a_cpu_clk_postmux1 }, 
};
static MESON_MUX(g12a_cpu_clk_dyn, HHI_SYS_CPU_CLK_CNTL0, 0x1, 10, NULL, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_dyn_parent_table, 2, 0);
const struct clk_parent_data [] g12a_cpu_clk_parent_table = {
    { .clk = &g12a_cpu_clk_dyn }, 
    { .clk = &g12a_sys_pll }, 
};
static MESON_MUX(g12a_cpu_clk, HHI_SYS_CPU_CLK_CNTL0, 0x1, 11, NULL, CLK_MUX_ROUND_CLOSEST, g12a_cpu_clk_parent_table, 2, 0);
const struct clk_parent_data [] g12b_cpu_clk_parent_table = {
    { .clk = &g12a_cpu_clk_dyn }, 
    { .clk = &g12b_sys1_pll }, 
};
static MESON_MUX(g12b_cpu_clk, HHI_SYS_CPU_CLK_CNTL0, 0x1, 11, NULL, CLK_MUX_ROUND_CLOSEST, g12b_cpu_clk_parent_table, 2, 0);
static MESON_MUX(g12b_cpub_clk_premux0, HHI_SYS_CPUB_CLK_CNTL, 0x3, 0, NULL, CLK_MUX_ROUND_CLOSEST, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_fclk_div2.hw },
			{ .hw = &g12a_fclk_div3.hw },
		}, 3, 0);
static struct clk g12b_cpub_clk_mux0_div = { 
	.data = &(struct meson_clk_cpu_dyndiv_data){
		.div = {
			.reg_off = HHI_SYS_CPUB_CLK_CNTL,
			.shift = 4,
			.width = 6,
		},
		.dyn = {
			.reg_off = HHI_SYS_CPUB_CLK_CNTL,
			.shift = 26,
			.width = 1,
		},
	},
	.init = &(struct clk_init_data){
		.name = "cpub_clk_dyn0_div",
		.ops = &meson_clk_cpu_dyndiv_ops,
		.parent_clks = (const struct clk *[]) {
			&g12b_cpub_clk_premux0
		},
		.num_parents = 1,
		.flags = CLK_SET_RATE_PARENT,
	},
};
const struct clk_parent_data [] g12b_cpub_clk_postmux0_parent_table = {
    { .clk = &g12b_cpub_clk_premux0 }, 
    { .clk = &g12b_cpub_clk_mux0_div }, 
};
static MESON_MUX(g12b_cpub_clk_postmux0, HHI_SYS_CPUB_CLK_CNTL, 0x1, 2, NULL, CLK_MUX_ROUND_CLOSEST, g12b_cpub_clk_postmux0_parent_table, 2, 0);
static MESON_MUX(g12b_cpub_clk_premux1, HHI_SYS_CPUB_CLK_CNTL, 0x3, 16, NULL, 0, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_fclk_div2.hw },
			{ .hw = &g12a_fclk_div3.hw },
		}, 3, 0);
static MESON_DIV_RO(g12b_cpub_clk_mux1_div, HHI_SYS_CPUB_CLK_CNTL, 20, 6, 0, { &g12b_cpub_clk_premux1 }, 1, 0);
const struct clk_parent_data [] g12b_cpub_clk_postmux1_parent_table = {
    { .clk = &g12b_cpub_clk_premux1 }, 
    { .clk = &g12b_cpub_clk_mux1_div }, 
};
static MESON_MUX(g12b_cpub_clk_postmux1, HHI_SYS_CPUB_CLK_CNTL, 0x1, 18, NULL, 0, g12b_cpub_clk_postmux1_parent_table, 2, 0);
const struct clk_parent_data [] g12b_cpub_clk_dyn_parent_table = {
    { .clk = &g12b_cpub_clk_postmux0 }, 
    { .clk = &g12b_cpub_clk_postmux1 }, 
};
static MESON_MUX(g12b_cpub_clk_dyn, HHI_SYS_CPUB_CLK_CNTL, 0x1, 10, NULL, CLK_MUX_ROUND_CLOSEST, g12b_cpub_clk_dyn_parent_table, 2, 0);
const struct clk_parent_data [] g12b_cpub_clk_parent_table = {
    { .clk = &g12b_cpub_clk_dyn }, 
    { .clk = &g12a_sys_pll }, 
};
static MESON_MUX(g12b_cpub_clk, HHI_SYS_CPUB_CLK_CNTL, 0x1, 11, NULL, CLK_MUX_ROUND_CLOSEST, g12b_cpub_clk_parent_table, 2, 0);
static MESON_MUX_RO(sm1_dsu_clk_premux0, HHI_SYS_CPU_CLK_CNTL5, 0x3, 0, NULL, 0, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_fclk_div2.hw },
			{ .hw = &g12a_fclk_div3.hw },
			{ .hw = &sm1_gp1_pll.hw },
		}, 4, 0);
static MESON_MUX_RO(sm1_dsu_clk_premux1, HHI_SYS_CPU_CLK_CNTL5, 0x3, 16, NULL, 0, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_fclk_div2.hw },
			{ .hw = &g12a_fclk_div3.hw },
			{ .hw = &sm1_gp1_pll.hw },
		}, 4, 0);
static MESON_DIV_RO(sm1_dsu_clk_mux0_div, HHI_SYS_CPU_CLK_CNTL5, 4, 6, 0, { &sm1_dsu_clk_premux0 }, 1, 0);
static MESON_MUX_RO(sm1_dsu_clk_postmux0, HHI_SYS_CPU_CLK_CNTL5, 0x1, 2, NULL, 0, None, 2, 0);
static MESON_DIV_RO(sm1_dsu_clk_mux1_div, HHI_SYS_CPU_CLK_CNTL5, 20, 6, 0, { &sm1_dsu_clk_premux1 }, 1, 0);
static MESON_MUX_RO(sm1_dsu_clk_postmux1, HHI_SYS_CPU_CLK_CNTL5, 0x1, 18, NULL, 0, None, 2, 0);
static MESON_MUX_RO(sm1_dsu_clk_dyn, HHI_SYS_CPU_CLK_CNTL5, 0x1, 10, NULL, 0, None, 2, 0);
static MESON_MUX_RO(sm1_dsu_final_clk, HHI_SYS_CPU_CLK_CNTL5, 0x1, 11, NULL, 0, None, 2, 0);
static MESON_MUX_RO(sm1_cpu1_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 24, NULL, 0, None, 1, 0);
static MESON_MUX_RO(sm1_cpu2_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 25, NULL, 0, None, 1, 0);
static MESON_MUX_RO(sm1_cpu3_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 26, NULL, 0, None, 1, 0);
static MESON_MUX_RO(sm1_dsu_clk, HHI_SYS_CPU_CLK_CNTL6, 0x1, 27, NULL, 0, None, 2, 0);
static MESON_GATE_RO(g12a_cpu_clk_div16_en, HHI_SYS_CPU_CLK_CNTL1, 1, 0, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12b_cpub_clk_div16_en, HHI_SYS_CPUB_CLK_CNTL1, 1, 0, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12a_cpu_clk_div16, 1, 16, { &g12a_cpu_clk_div16_en }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div16, 1, 16, { &g12b_cpub_clk_div16_en }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_apb_div, HHI_SYS_CPU_CLK_CNTL1, 3, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_apb, HHI_SYS_CPU_CLK_CNTL1, 1, 0, { &g12a_cpu_clk_apb_div }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_atb_div, HHI_SYS_CPU_CLK_CNTL1, 6, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_atb, HHI_SYS_CPU_CLK_CNTL1, 17, 0, { &g12a_cpu_clk_atb_div }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_axi_div, HHI_SYS_CPU_CLK_CNTL1, 9, 3, CLK_DIVIDER_POWER_OF_TWO, { &g12a_cpu_clk }, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_axi, HHI_SYS_CPU_CLK_CNTL1, 18, 0, { &g12a_cpu_clk_axi_div }, 1, 0);
static MESON_DIV_RO(g12a_cpu_clk_trace_div, HHI_SYS_CPU_CLK_CNTL1, 20, 3, CLK_DIVIDER_POWER_OF_TWO, None, 1, 0);
static MESON_GATE_RO(g12a_cpu_clk_trace, HHI_SYS_CPU_CLK_CNTL1, 23, 0, { &g12a_cpu_clk_trace_div }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div2, 1, 2, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div3, 1, 3, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div4, 1, 4, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div5, 1, 5, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div6, 1, 6, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div7, 1, 7, { &g12b_cpub_clk }, 1, 0);
static MESON_FIXED_FACTOR(g12b_cpub_clk_div8, 1, 8, { &g12b_cpub_clk }, 1, 0);
static MESON_MUX_RO(g12b_cpub_clk_apb_sel, HHI_SYS_CPUB_CLK_CNTL1, 7, 3, mux_table_cpub, 0, None, 7, 0);
static MESON_GATE_RO(g12b_cpub_clk_apb, HHI_SYS_CPUB_CLK_CNTL1, 16, CLK_GATE_SET_TO_DISABLE, { &g12b_cpub_clk_apb_sel }, 1, 0);
static MESON_MUX_RO(g12b_cpub_clk_atb_sel, HHI_SYS_CPUB_CLK_CNTL1, 7, 6, mux_table_cpub, 0, None, 7, 0);
static MESON_GATE_RO(g12b_cpub_clk_atb, HHI_SYS_CPUB_CLK_CNTL1, 17, CLK_GATE_SET_TO_DISABLE, { &g12b_cpub_clk_atb_sel }, 1, 0);
static MESON_MUX_RO(g12b_cpub_clk_axi_sel, HHI_SYS_CPUB_CLK_CNTL1, 7, 9, mux_table_cpub, 0, None, 7, 0);
static MESON_GATE_RO(g12b_cpub_clk_axi, HHI_SYS_CPUB_CLK_CNTL1, 18, CLK_GATE_SET_TO_DISABLE, { &g12b_cpub_clk_axi_sel }, 1, 0);
static MESON_MUX_RO(g12b_cpub_clk_trace_sel, HHI_SYS_CPUB_CLK_CNTL1, 7, 20, mux_table_cpub, 0, None, 7, 0);
static MESON_GATE_RO(g12b_cpub_clk_trace, HHI_SYS_CPUB_CLK_CNTL1, 23, CLK_GATE_SET_TO_DISABLE, { &g12b_cpub_clk_trace_sel }, 1, 0);
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
		.range = &g12a_gp0_pll_mult_range,
		.init_regs = g12a_gp0_init_regs,
		.init_count = ARRAY_SIZE(g12a_gp0_init_regs),
	},
	.init = &(struct clk_init_data){
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
	.init = &(struct clk_init_data){
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
		.range = &g12a_gp0_pll_mult_range,
		.init_regs = g12a_hifi_init_regs,
		.init_count = ARRAY_SIZE(g12a_hifi_init_regs),
		.flags = CLK_MESON_PLL_ROUND_CLOSEST,
	},
	.init = &(struct clk_init_data){
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
	.init = &(struct clk_init_data){
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
	.init = &(struct clk_init_data){
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
static MESON_MUX_RO(g12a_mpll_50m, HHI_FIX_PLL_CNTL3, 0x1, 5, NULL, 0, (const struct clk_parent_data []) {
			{ .fw_name = "xtal", },
			{ .hw = &g12a_mpll_50m_div.hw },
		}, 2, 0);
static MESON_FIXED_FACTOR(g12a_mpll_prediv, 1, 2, { &g12a_fixed_pll_dco }, 1, 0);
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
			.width	 = 1,
		},
		.n2 = {
			.reg_off = HHI_MPLL_CNTL1,
			.shift   = 20,
			.width   = 9,
		},
		.ssen = {
			.reg_off = HHI_MPLL_CNTL1,
			.shift   = 29,
			.width	 = 1,
		},
		.lock = &meson_clk_lock,
		.init_regs = g12a_mpll0_init_regs,
		.init_count = ARRAY_SIZE(g12a_mpll0_init_regs),
	},
	.init = &(struct clk_init_data){
		.name = "mpll0_div",
		.ops = &meson_clk_mpll_ops,
		.parent_clks = (const struct clk *[]) {
			&g12a_mpll_prediv
		},
		.num_parents = 1,
	},
};
static MESON_GATE(g12a_mpll0, HHI_MPLL_CNTL1, 31, 0, { &g12a_mpll0_div }, 1, 0);
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
			.width	 = 1,
		},
		.n2 = {
			.reg_off = HHI_MPLL_CNTL3,
			.shift   = 20,
			.width   = 9,
		},
		.ssen = {
			.reg_off = HHI_MPLL_CNTL3,
			.shift   = 29,
			.width	 = 1,
		},
		.lock = &meson_clk_lock,
		.init_regs = g12a_mpll1_init_regs,
		.init_count = ARRAY_SIZE(g12a_mpll1_init_regs),
	},
	.init = &(struct clk_init_data){
		.name = "mpll1_div",
		.ops = &meson_clk_mpll_ops,
		.parent_clks = (const struct clk *[]) {
			&g12a_mpll_prediv
		},
		.num_parents = 1,
	},
};
static MESON_GATE(g12a_mpll1, HHI_MPLL_CNTL3, 31, 0, { &g12a_mpll1_div }, 1, 0);
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
			.width	 = 1,
		},
		.n2 = {
			.reg_off = HHI_MPLL_CNTL5,
			.shift   = 20,
			.width   = 9,
		},
		.ssen = {
			.reg_off = HHI_MPLL_CNTL5,
			.shift   = 29,
			.width	 = 1,
		},
		.lock = &meson_clk_lock,
		.init_regs = g12a_mpll2_init_regs,
		.init_count = ARRAY_SIZE(g12a_mpll2_init_regs),
	},
	.init = &(struct clk_init_data){
		.name = "mpll2_div",
		.ops = &meson_clk_mpll_ops,
		.parent_clks = (const struct clk *[]) {
			&g12a_mpll_prediv
		},
		.num_parents = 1,
	},
};
static MESON_GATE(g12a_mpll2, HHI_MPLL_CNTL5, 31, 0, { &g12a_mpll2_div }, 1, 0);
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
		.lock = &meson_clk_lock,
		.init_regs = g12a_mpll3_init_regs,
		.init_count = ARRAY_SIZE(g12a_mpll3_init_regs),
	},
	.init = &(struct clk_init_data){
		.name = "mpll3_div",
		.ops = &meson_clk_mpll_ops,
		.parent_clks = (const struct clk *[]) {
			&g12a_mpll_prediv
		},
		.num_parents = 1,
	},
};
static MESON_GATE(g12a_mpll3, HHI_MPLL_CNTL7, 31, 0, { &g12a_mpll3_div }, 1, 0);
static MESON_MUX_RO(g12a_mpeg_clk_sel, HHI_MPEG_CLK_CNTL, 0x7, 12, mux_table_clk81, 0, clk81_parent_data, 0, 0);
static MESON_DIV(g12a_mpeg_clk_div, HHI_MPEG_CLK_CNTL, 0, 7, 0, { &g12a_mpeg_clk_sel }, 1, 0);
static MESON_GATE(g12a_clk81, HHI_MPEG_CLK_CNTL, 7, 0, { &g12a_mpeg_clk_div }, 1, 0);
static MESON_MUX(g12a_sd_emmc_a_clk0_sel, HHI_SD_EMMC_CLK_CNTL, 0x7, 9, NULL, 0, g12a_sd_emmc_clk0_parent_data, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_sd_emmc_a_clk0_div, HHI_SD_EMMC_CLK_CNTL, 0, 7, 0, { &g12a_sd_emmc_a_clk0_sel }, 1, 0);
static MESON_GATE(g12a_sd_emmc_a_clk0, HHI_SD_EMMC_CLK_CNTL, 7, 0, { &g12a_sd_emmc_a_clk0_div }, 1, 0);
static MESON_MUX(g12a_sd_emmc_b_clk0_sel, HHI_SD_EMMC_CLK_CNTL, 0x7, 25, NULL, 0, g12a_sd_emmc_clk0_parent_data, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_sd_emmc_b_clk0_div, HHI_SD_EMMC_CLK_CNTL, 16, 7, 0, { &g12a_sd_emmc_b_clk0_sel }, 1, 0);
static MESON_GATE(g12a_sd_emmc_b_clk0, HHI_SD_EMMC_CLK_CNTL, 23, 0, { &g12a_sd_emmc_b_clk0_div }, 1, 0);
static MESON_MUX(g12a_sd_emmc_c_clk0_sel, HHI_NAND_CLK_CNTL, 0x7, 9, NULL, 0, g12a_sd_emmc_clk0_parent_data, 0, CLK_SET_RATE_PARENT);
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
	.init = &(struct clk_init_data) {
		.name = "vid_pll_div",
		.ops = &meson_vid_pll_div_ro_ops,
		.parent_clks = (const struct clk *[]) { &g12a_hdmi_pll },
		.num_parents = 1,
		.flags = CLK_SET_RATE_PARENT | CLK_GET_RATE_NOCACHE,
	},
};
static MESON_MUX(g12a_vid_pll_sel, HHI_VID_PLL_CLK_DIV, 0x1, 18, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_GATE(g12a_vid_pll, HHI_VID_PLL_CLK_DIV, 19, 0, { &g12a_vid_pll_sel }, 1, 0);
static MESON_MUX(g12a_vpu_0_sel, HHI_VPU_CLK_CNTL, 0x7, 9, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vpu_0_div, HHI_VPU_CLK_CNTL, 0, 7, 0, { &g12a_vpu_0_sel }, 1, 0);
static MESON_GATE(g12a_vpu_0, HHI_VPU_CLK_CNTL, 8, 0, { &g12a_vpu_0_div }, 1, 0);
static MESON_MUX(g12a_vpu_1_sel, HHI_VPU_CLK_CNTL, 0x7, 25, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vpu_1_div, HHI_VPU_CLK_CNTL, 16, 7, 0, { &g12a_vpu_1_sel }, 1, 0);
static MESON_GATE(g12a_vpu_1, HHI_VPU_CLK_CNTL, 24, 0, { &g12a_vpu_1_div }, 1, 0);
const struct clk_parent_data [] g12a_vpu_parent_table = {
    { .clk = &g12a_vpu_0 }, 
    { .clk = &g12a_vpu_1 }, 
};
static MESON_MUX(g12a_vpu, HHI_VPU_CLK_CNTL, 1, 31, NULL, 0, g12a_vpu_parent_table, 2, 0);
static MESON_MUX(g12a_vdec_1_sel, HHI_VDEC_CLK_CNTL, 0x7, 9, NULL, CLK_MUX_ROUND_CLOSEST, None, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_vdec_1_div, HHI_VDEC_CLK_CNTL, 0, 7, CLK_DIVIDER_ROUND_CLOSEST, { &g12a_vdec_1_sel }, 1, 0);
static MESON_GATE(g12a_vdec_1, HHI_VDEC_CLK_CNTL, 8, 0, { &g12a_vdec_1_div }, 1, 0);
static MESON_MUX(g12a_vdec_hevcf_sel, HHI_VDEC2_CLK_CNTL, 0x7, 9, NULL, CLK_MUX_ROUND_CLOSEST, None, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_vdec_hevcf_div, HHI_VDEC2_CLK_CNTL, 0, 7, CLK_DIVIDER_ROUND_CLOSEST, { &g12a_vdec_hevcf_sel }, 1, 0);
static MESON_GATE(g12a_vdec_hevcf, HHI_VDEC2_CLK_CNTL, 8, 0, { &g12a_vdec_hevcf_div }, 1, 0);
static MESON_MUX(g12a_vdec_hevc_sel, HHI_VDEC2_CLK_CNTL, 0x7, 25, NULL, CLK_MUX_ROUND_CLOSEST, None, 0, CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_vdec_hevc_div, HHI_VDEC2_CLK_CNTL, 16, 7, CLK_DIVIDER_ROUND_CLOSEST, { &g12a_vdec_hevc_sel }, 1, 0);
static MESON_GATE(g12a_vdec_hevc, HHI_VDEC2_CLK_CNTL, 24, 0, { &g12a_vdec_hevc_div }, 1, 0);
static MESON_MUX(g12a_vapb_0_sel, HHI_VAPBCLK_CNTL, 0x3, 9, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vapb_0_div, HHI_VAPBCLK_CNTL, 0, 7, 0, { &g12a_vapb_0_sel }, 1, 0);
static MESON_GATE(g12a_vapb_0, HHI_VAPBCLK_CNTL, 8, 0, { &g12a_vapb_0_div }, 1, 0);
static MESON_MUX(g12a_vapb_1_sel, HHI_VAPBCLK_CNTL, 0x3, 25, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT);
static MESON_DIV(g12a_vapb_1_div, HHI_VAPBCLK_CNTL, 16, 7, 0, { &g12a_vapb_1_sel }, 1, 0);
static MESON_GATE(g12a_vapb_1, HHI_VAPBCLK_CNTL, 24, 0, { &g12a_vapb_1_div }, 1, 0);
const struct clk_parent_data [] g12a_vapb_sel_parent_table = {
    { .clk = &g12a_vapb_0 }, 
    { .clk = &g12a_vapb_1 }, 
};
static MESON_MUX(g12a_vapb_sel, HHI_VAPBCLK_CNTL, 1, 31, NULL, 0, g12a_vapb_sel_parent_table, 2, 0);
static MESON_GATE(g12a_vapb, HHI_VAPBCLK_CNTL, 30, 0, { &g12a_vapb_sel }, 1, 0);
static MESON_MUX(g12a_vclk_sel, HHI_VID_CLK_CNTL, 0x7, 16, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_vclk2_sel, HHI_VIID_CLK_CNTL, 0x7, 16, NULL, 0, None, 0, CLK_SET_RATE_NO_REPARENT);
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
	.init = &(struct clk_init_data){
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
	.init = &(struct clk_init_data) {
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
static MESON_MUX(g12a_cts_enci_sel, HHI_VID_CLK_DIV, 0xf, 28, mux_table_cts_sel, 0, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_cts_encp_sel, HHI_VID_CLK_DIV, 0xf, 20, mux_table_cts_sel, 0, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_cts_encl_sel, HHI_VIID_CLK_DIV, 0xf, 12, mux_table_cts_sel, 0, None, 0, CLK_SET_RATE_PARENT | CLK_SET_RATE_NO_REPARENT);
static MESON_MUX(g12a_cts_vdac_sel, HHI_VIID_CLK_DIV, 0xf, 28, mux_table_cts_sel, 0, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_MUX(g12a_hdmi_tx_sel, HHI_HDMI_CLK_CNTL, 0xf, 16, mux_table_hdmi_tx_sel, 0, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_GATE(g12a_cts_enci, HHI_VID_CLK_CNTL2, 0, 0, { &g12a_cts_enci_sel }, 1, 0);
static MESON_GATE(g12a_cts_encp, HHI_VID_CLK_CNTL2, 2, 0, { &g12a_cts_encp_sel }, 1, 0);
static MESON_GATE(g12a_cts_encl, HHI_VID_CLK_CNTL2, 3, 0, { &g12a_cts_encl_sel }, 1, 0);
static MESON_GATE(g12a_cts_vdac, HHI_VID_CLK_CNTL2, 4, 0, { &g12a_cts_vdac_sel }, 1, 0);
static MESON_GATE(g12a_hdmi_tx, HHI_VID_CLK_CNTL2, 5, 0, { &g12a_hdmi_tx_sel }, 1, 0);
static MESON_MUX(g12a_mipi_dsi_pxclk_sel, HHI_MIPIDSI_PHY_CLK_CNTL, 0x7, 12, NULL, CLK_MUX_ROUND_CLOSEST, None, 0, CLK_SET_RATE_NO_REPARENT | CLK_SET_RATE_PARENT);
static MESON_DIV(g12a_mipi_dsi_pxclk_div, HHI_MIPIDSI_PHY_CLK_CNTL, 0, 7, 0, { &g12a_mipi_dsi_pxclk_sel }, 1, 0);
static MESON_GATE(g12a_mipi_dsi_pxclk, HHI_MIPIDSI_PHY_CLK_CNTL, 8, 0, { &g12a_mipi_dsi_pxclk_div }, 1, 0);
static MESON_MUX(g12b_mipi_isp_sel, HHI_ISP_CLK_CNTL, 7, 9, NULL, 0, g12b_mipi_isp_parent_data, 0, 0);
static MESON_DIV(g12b_mipi_isp_div, HHI_ISP_CLK_CNTL, 0, 7, 0, { &g12b_mipi_isp_sel }, 1, 0);
static MESON_GATE(g12b_mipi_isp, HHI_ISP_CLK_CNTL, 8, 0, { &g12b_mipi_isp_div }, 1, 0);
static MESON_MUX(g12a_hdmi_sel, HHI_HDMI_CLK_CNTL, 0x3, 9, NULL, CLK_MUX_ROUND_CLOSEST, g12a_hdmi_parent_data, 0, CLK_SET_RATE_NO_REPARENT | CLK_GET_RATE_NOCACHE);
static MESON_DIV(g12a_hdmi_div, HHI_HDMI_CLK_CNTL, 0, 7, 0, { &g12a_hdmi_sel }, 1, 0);
static MESON_GATE(g12a_hdmi, HHI_HDMI_CLK_CNTL, 8, 0, { &g12a_hdmi_div }, 1, 0);
static MESON_MUX(g12a_mali_0_sel, HHI_MALI_CLK_CNTL, 0x7, 9, NULL, 0, g12a_mali_0_1_parent_data, 8, 0);
static MESON_DIV(g12a_mali_0_div, HHI_MALI_CLK_CNTL, 0, 7, 0, { &g12a_mali_0_sel }, 1, 0);
static MESON_GATE(g12a_mali_0, HHI_MALI_CLK_CNTL, 8, 0, { &g12a_mali_0_div }, 1, 0);
static MESON_MUX(g12a_mali_1_sel, HHI_MALI_CLK_CNTL, 0x7, 25, NULL, 0, g12a_mali_0_1_parent_data, 8, 0);
static MESON_DIV(g12a_mali_1_div, HHI_MALI_CLK_CNTL, 16, 7, 0, { &g12a_mali_1_sel }, 1, 0);
static MESON_GATE(g12a_mali_1, HHI_MALI_CLK_CNTL, 24, 0, { &g12a_mali_1_div }, 1, 0);
static MESON_MUX(g12a_mali, HHI_MALI_CLK_CNTL, 1, 31, NULL, 0, None, 2, CLK_SET_RATE_PARENT);
static MESON_DIV_RO(g12a_ts_div, HHI_TS_CLK_CNTL, 0, 8, 0, None, 1, 0);
static MESON_GATE(g12a_ts, HHI_TS_CLK_CNTL, 8, 0, { &g12a_ts_div }, 1, 0);
static MESON_MUX(g12a_spicc0_sclk_sel, HHI_SPICC_CLK_CNTL, 7, 7, NULL, 0, spicc_sclk_parent_data, 0, 0);
static MESON_DIV(g12a_spicc0_sclk_div, HHI_SPICC_CLK_CNTL, 0, 6, 0, { &g12a_spicc0_sclk_sel }, 1, 0);
static MESON_GATE(g12a_spicc0_sclk, HHI_SPICC_CLK_CNTL, 6, 0, { &g12a_spicc0_sclk_div }, 1, 0);
static MESON_MUX(g12a_spicc1_sclk_sel, HHI_SPICC_CLK_CNTL, 7, 23, NULL, 0, spicc_sclk_parent_data, 0, 0);
static MESON_DIV(g12a_spicc1_sclk_div, HHI_SPICC_CLK_CNTL, 16, 6, 0, { &g12a_spicc1_sclk_sel }, 1, 0);
static MESON_GATE(g12a_spicc1_sclk, HHI_SPICC_CLK_CNTL, 22, 0, { &g12a_spicc1_sclk_div }, 1, 0);
static MESON_MUX(sm1_nna_axi_clk_sel, HHI_NNA_CLK_CNTL, 7, 9, NULL, 0, nna_clk_parent_data, 0, 0);
static MESON_DIV(sm1_nna_axi_clk_div, HHI_NNA_CLK_CNTL, 0, 7, 0, { &sm1_nna_axi_clk_sel }, 1, 0);
static MESON_GATE(sm1_nna_axi_clk, HHI_NNA_CLK_CNTL, 8, 0, { &sm1_nna_axi_clk_div }, 1, 0);
static MESON_MUX(sm1_nna_core_clk_sel, HHI_NNA_CLK_CNTL, 7, 25, NULL, 0, nna_clk_parent_data, 0, 0);
static MESON_DIV(sm1_nna_core_clk_div, HHI_NNA_CLK_CNTL, 16, 7, 0, { &sm1_nna_core_clk_sel }, 1, 0);
static MESON_GATE(sm1_nna_core_clk, HHI_NNA_CLK_CNTL, 24, 0, { &sm1_nna_core_clk_div }, 1, 0);
