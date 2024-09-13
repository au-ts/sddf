#ifndef CLK_CONFIG_H_
#define CLK_CONFIG_H_


#include <stdint.h>

struct clk_cfg {
    uint32_t clk_id;
    uint32_t frequency;
};

#define NUM_DEVICE_CLKS 1
static struct clk_cfg *enabled_hw_clks[] = {
    &(struct clk_cfg) {
        .clk_id = 0x18,
        .frequency = 1,
    }
};

#endif // CLK_CONFIG_H_
