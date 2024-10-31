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

static unsigned long imx8m_clk_core_slice_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct clk_core_slice_data *data = (struct clk_core_slice_data *)(clk->data);

    uint32_t div_val = regmap_read_bits(clk->base, data->offset, data->div_shift, data->div_width);
    /* Divider value is n+1 */
    return DIV_ROUND_UP_ULL((uint64_t)prate, div_val + 1);
}

static uint8_t imx8m_clk_core_slice_get_parent(const struct clk *clk)
{
    struct clk_core_slice_data *data = (struct clk_core_slice_data *)(clk->data);

    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_mux_read_bits(clk->base, data->offset, data->mux_shift, data->mux_mask);

    if (val >= num_parents)
        return -1;

    return val;
}

static int imx8m_clk_core_slice_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_core_slice_data *data = (struct clk_core_slice_data *)(clk->data);

    /*
     * write twice to make sure non-target interface
     * SEL_A/B point the same clk input.
     */
    regmap_mux_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);
    regmap_mux_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);

    return 0;
}

const struct clk_ops clk_core_slice_ops = {
    .recalc_rate = imx8m_clk_core_slice_recalc_rate,
    /* .round_rate = imx8m_clk_core_slice_round_rate, */
    /* .set_rate = imx8m_clk_core_slice_set_rate, */
    /* .determine_rate = imx8m_clk_core_slice_determine_rate, */
    .get_parent = imx8m_clk_core_slice_get_parent,
    .set_parent = imx8m_clk_core_slice_set_parent,
};

static unsigned long imx8m_clk_common_slice_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct clk_common_slice_data *data = (struct clk_common_slice_data *)(clk->data);

    uint32_t prediv_val = regmap_read_bits(clk->base, data->offset, data->prevdiv_shift, data->prevdiv_width);
    /* Divider value is n+1 */
    unsigned long prediv_rate = DIV_ROUND_UP_ULL((uint64_t)prate, prediv_val + 1);

    uint32_t postdiv_val = regmap_read_bits(clk->base, data->offset, data->postdiv_shift, data->postdiv_width);
    /* Divider value is n+1 */
    return DIV_ROUND_UP_ULL((uint64_t)prediv_rate, postdiv_val + 1);
}

static uint8_t imx8m_clk_common_slice_get_parent(const struct clk *clk)
{
    struct clk_common_slice_data *data = (struct clk_common_slice_data *)(clk->data);

    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_mux_read_bits(clk->base, data->offset, data->mux_shift, data->mux_mask);

    if (val >= num_parents)
        return -1;

    return val;
}

static int imx8m_clk_common_slice_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_common_slice_data *data = (struct clk_common_slice_data *)(clk->data);

    /*
     * write twice to make sure non-target interface
     * SEL_A/B point the same clk input.
     */
    regmap_mux_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);
    regmap_mux_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);

    return 0;
}

const struct clk_ops clk_common_slice_ops = {
    .recalc_rate = imx8m_clk_common_slice_recalc_rate,
    /* .round_rate = imx8m_clk_common_slice_round_rate, */
    /* .set_rate = imx8m_clk_common_slice_set_rate, */
    /* .determine_rate = imx8m_clk_common_slice_determine_rate, */
    .get_parent = imx8m_clk_common_slice_get_parent,
    .set_parent = imx8m_clk_common_slice_set_parent,
};

static unsigned long imx8m_clk_bus_slice_recalc_rate(const struct clk *clk,
                                unsigned long prate)
{
    struct clk_bus_slice_data *data = (struct clk_bus_slice_data *)(clk->data);

    uint32_t prediv_val = regmap_read_bits(clk->base, data->offset, data->prevdiv_shift, data->prevdiv_width);
    /* Divider value is n+1 */
    unsigned long prediv_rate = DIV_ROUND_UP_ULL((uint64_t)prate, prediv_val + 1);

    uint32_t postdiv_val = regmap_read_bits(clk->base, data->offset, data->postdiv_shift, data->postdiv_width);
    /* Divider value is n+1 */
    return DIV_ROUND_UP_ULL((uint64_t)prediv_rate, postdiv_val + 1);
}

static uint8_t imx8m_clk_bus_slice_get_parent(const struct clk *clk)
{
    struct clk_bus_slice_data *data = (struct clk_bus_slice_data *)(clk->data);

    uint32_t num_parents = clk->hw.init->num_parents;
    uint32_t val = regmap_mux_read_bits(clk->base, data->offset, data->mux_shift, data->mux_mask);

    if (val >= num_parents)
        return -1;

    return val;
}

static int imx8m_clk_bus_slice_set_parent(struct clk *clk, uint8_t index)
{
    struct clk_bus_slice_data *data = (struct clk_bus_slice_data *)(clk->data);

    /*
     * write twice to make sure non-target interface
     * SEL_A/B point the same clk input.
     */
    regmap_mux_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);
    regmap_mux_update_bits(clk->base, data->offset, data->mux_shift, data->mux_mask, index);

    return 0;
}

const struct clk_ops clk_bus_slice_ops = {
    .recalc_rate = imx8m_clk_bus_slice_recalc_rate,
    /* .round_rate = imx8m_clk_composite_divider_round_rate, */
    /* .set_rate = imx8m_clk_composite_divider_set_rate, */
    /* .determine_rate = imx8m_divider_determine_rate, */
    .get_parent = imx8m_clk_bus_slice_get_parent,
    .set_parent = imx8m_clk_bus_slice_set_parent,
};
