#ifndef CLK_OPERATIONS_H_
#define CLK_OPERATIONS_H_

#include <clk.h>

#define MASK(width)  ((1 << width) - 1)
#define DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))
#define do_div(n,base) ({                       \
    uint32_t __base = (base);                   \
    uint32_t __rem;                             \
    __rem = ((uint64_t)(n)) % __base;           \
    (n) = ((uint64_t)(n)) / __base;             \
    __rem;                                      \
 })
#define DIV_ROUND_DOWN_ULL(ll, d) \
    ({ uint64_t _tmp = (ll); do_div(_tmp, d); _tmp; })
#define DIV_ROUND_UP_ULL(ll, d) \
    DIV_ROUND_DOWN_ULL((uint64_t)(ll) + (d) - 1, (d))

extern void init_clk_base(uintptr_t base_addr);

extern const struct clk_ops clk_regmap_gate_ops;
extern const struct clk_ops clk_regmap_gate_ro_ops;
extern const struct clk_ops clk_regmap_divider_ops;
extern const struct clk_ops clk_regmap_divider_ro_ops;
extern const struct clk_ops clk_regmap_mux_ro_ops;
extern const struct clk_ops clk_fixed_factor_ops;
extern const struct clk_ops meson_clk_pll_ro_ops;

#endif // CLK_OPERATIONS_H_
