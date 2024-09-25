#include <clk.h>

struct clk_cfg {
    uint32_t clk_id;
    uint32_t frequency;
};

#define NUM_DEVICE_CLKS 4
static struct clk_cfg clk_configs[] = {
    { .clk_id = 0x18, .frequency = 0, },
    { .clk_id = 0x0b, .frequency = 0x10266000, },
    { .clk_id = 0x0c, .frequency = 0x17700000, },
    { .clk_id = 0x0d, .frequency = 0x11940000, },
};
