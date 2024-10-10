#ifndef CLK_IMX8MM_H_
#define CLK_IMX8MM_H_

#define IMX_CLK_MUX_FLAGS(_name, _offset, _shift, _width, _parent_data, _num_parents, data_flags) \
CLK_MUX(_name, _offset, MASK(_width), _shift, 0, _data_flags, _parent_data, _num_parent, 0)

#define IMX_CLK_MUX(_name, _offset, _shift, _width, _parent_data, _num_parents) \
CLK_MUX(_name, _offset, MASK(_width), _shift, 0, 0, _parent_data, _num_parent, 0)

#define IMX_CLK_DIVIDER(_name, _parent_clks, _offset, _shift, _width) \
CLK_DIV(_name, _offset, _shift, _width, 0, _parent_clks, 1, CLK_SET_RATE_PARENT)

#define IMX_CLK_FRAC_PLL(_name, _parent_clks, _offset)      \
struct clk _name = {                                        \
    .data = &(struct clk_frac_pll) {                        \
        .offset = (_offset),                                \
    },                                                      \
    .hw.init = &(struct clk_init_data) {                    \
        .name = #_name,                                     \
        .ops = &clk_frac_pll_ops,                           \
        .parent_clks = _parent_clks,                        \
        .num_parents = 1,                                   \
        .flag = 0,                                          \
    },                                                      \
}

#define IMX_CLK_GATE(_name, _parent_clks, _offset, _shift)  \
CLK_GATE(_name, _offset, _shift, 0, _parent_clks, 1, 0)

#define IMX_CLK_FIXED_FACTOR(_name, _parent_clks, _mult, _div)  \
CLK_FIXED_FACTOR(_name, _mult, _div, 0, _parent_clks, 1, CLK_SET_RATE_PARENT)


struct clk **get_clk_list(void);

#endif // CLK_IMX8MM_H_
