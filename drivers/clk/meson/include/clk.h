#ifndef CLK_H_
#define CLK_H_

#include <stdint.h>

#define BIT(nr) (1UL << (nr))

struct clk_hw {
    uint32_t reg_offset;
    uint32_t bit_idx;
};

struct clk_ops {
    int (*enable)(uintptr_t clk_base, struct clk_hw *hw);
    void (*disable)(uintptr_t clk_base, struct clk_hw *hw);
};

struct clk {
	struct clk_hw hw;
	const struct clk_ops *ops;
};

#endif // CLK_H_
