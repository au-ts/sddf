#include <utils.h>
#include <clk-operations.h>
#include <clk-imx.h>

static int clk_gate2_enable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    return regmap_update_bits(clk->base, data->offset, data->bit_idx, 2, 0x3);
}

static int clk_gate2_disable(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    return regmap_update_bits(clk->base, data->offset, data->bit_idx, 2, 0);
}

static int clk_gate2_is_enabled(struct clk *clk)
{
    struct clk_gate_data *data = (struct clk_gate_data *)(clk->data);

    if (regmap_read_bits(clk->base, data->offset, data->bit_idx, 2) == 0x3)
        return 1;

    return 0;
}

const struct clk_ops clk_gate2_ops = {
    .enable = clk_gate2_enable,
    .disable = clk_gate2_disable,
    /* .disable_unused = clk_gate2_disable_unused, */
    .is_enabled = clk_gate2_is_enabled,
};

const struct clk_ops clk_frac_pll_ops = {

};

const struct clk_ops clk_sscg_pll_ops = {

};

const struct clk_ops clk_core_slice_ops = {

};

const struct clk_ops clk_common_slice_ops = {

};

const struct clk_ops clk_bus_slice_ops = {

};
