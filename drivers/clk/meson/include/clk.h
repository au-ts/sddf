#ifndef CLK_H_
#define CLK_H_

#include <stdint.h>

#define BIT(nr) (1UL << (nr))

static uintptr_t clk_base;

struct clk;

struct clk_hw {
    struct clk_core *core;
    struct clk *clk;
    struct clk_init_data *init;
};


struct clk_ops {
    int (*set_rate)(struct clk_hw *hw, uint32_t rate, uint32_t parent_rate);
    int (*enable)(struct clk_hw *hw);
    void (*disable)(struct clk_hw *hw);
};

struct clk {
    struct clk_hw hw;
    void *data;
};

struct clk_core {
    /* struct clk_hw *hw; */
    uint32_t rate;          // TODO: Type?
};

struct clk_init_data {
    const char *name;
    const struct clk_ops *ops;
    const struct clk_hw **parent_hws;
    uint8_t num_parents;
    uint32_t flags;
};


struct clk_gate_data {
    uint32_t offset;
    uint8_t bit_idx;
    uint8_t flags;
};

struct clk_div_data {
    uint32_t offset;
    uint8_t shift;
    uint8_t width;
    uint8_t flags;
    /* const struct clk_div_table *table; */
};

struct clk_fixed_factor_data {
    uint32_t mul;
    uint32_t div;
};

struct clk_mux_data {
    uint32_t offset;
    uint32_t *table;
    uint32_t mask;
    uint8_t shift;
    uint8_t flags;
};

#endif // CLK_H_
