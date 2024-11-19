/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/clk/client.h>

#define CLK_DRIVER_CH 0

void init(void)
{
    sddf_dprintf("--------------------\n");
    sddf_dprintf("Clock Driver Test\n");

#ifdef TEST_BOARD_odroidc4
    sddf_dprintf("Test board: odroidc4\n");

    /**
     * CLKID_CLK81   = 10
     * CLKID_I2C     = 24
     * CLKID_CPU_CLK = 187
     *
     * see `sddf/drivers/clk/meson/include/g12a-bindings.h` for more clock indices.
     *
     **/
    uint32_t clk_id_to_enable = 10;
    int ret = sddf_clk_enable(CLK_DRIVER_CH, clk_id_to_enable);
    if (ret) {
        sddf_dprintf("Failed to enable clock %u: err - %d\n", clk_id_to_enable, ret);
    } else {
        sddf_dprintf("Successfully enabled clock %u\n", clk_id_to_enable);
    }

    uint32_t clk_id_to_disable = 24;
    ret = sddf_clk_disable(CLK_DRIVER_CH, clk_id_to_disable);
    if (ret) {
        sddf_dprintf("Failed to disable clock %u: err - %d\n", clk_id_to_enable, ret);
    } else {
        sddf_dprintf("Successfully disabled clock %u\n", clk_id_to_enable);
    }

    uint64_t rate = 0;
    uint32_t clk_id_to_set_rate = 10;
    ret = sddf_clk_get_rate(CLK_DRIVER_CH, clk_id_to_set_rate, &rate);
    if (ret) {
        sddf_dprintf("Failed to get the rate of clock %u: err - %d\n", clk_id_to_set_rate, ret);
    } else {
        sddf_dprintf("The rate of clock %u: %lu\n", clk_id_to_set_rate, rate);
    }

    ret = sddf_clk_set_rate(CLK_DRIVER_CH, clk_id_to_set_rate, 150000000, &rate);
    if (ret) {
        sddf_dprintf("Failed to set the rate of clock %u: err - %d\n", clk_id_to_set_rate, ret);
    } else {
        sddf_dprintf("Set the rate of clock %u to %lu\n", ret, rate);
    }

    uint32_t clk_id_to_get_rate = 187;
    ret = sddf_clk_get_rate(CLK_DRIVER_CH, clk_id_to_get_rate, &rate);
    if (ret) {
        sddf_dprintf("Failed to get the rate of clock %u: err - %d\n", clk_id_to_get_rate, ret);
    } else {
        sddf_dprintf("The rate of clock %u: %lu\n", clk_id_to_get_rate, rate);
    }

    uint32_t clk_id_to_test_parent = 63;
    uint32_t parent_id = 0;
    ret = sddf_clk_get_parent(CLK_DRIVER_CH, clk_id_to_test_parent, &parent_id);
    if (ret) {
        sddf_dprintf("Failed to get the parent of clock %u: err - %d\n", clk_id_to_test_parent, ret);
    } else {
        sddf_dprintf("The parent of clock %u: %u\n", clk_id_to_test_parent, parent_id);
    }

    uint32_t pclk_idx = 3;
    ret = sddf_clk_set_parent(CLK_DRIVER_CH, clk_id_to_test_parent, pclk_idx);
    if (ret) {
        sddf_dprintf("Failed to set the parent of clock %u: err - %d\n", clk_id_to_test_parent, ret);
    } else {
        ret = sddf_clk_get_parent(CLK_DRIVER_CH, clk_id_to_test_parent, &parent_id);
        sddf_dprintf("The parent of clock %u has been set to: %u\n", clk_id_to_test_parent, parent_id);
    }

#elif TEST_BOARD_maaxboard
    sddf_dprintf("Test board: maaxboard\n");
    int ret = 0;

    /**
     * IMX8MQ_CLK_SAI1_ROOT = 196
     * IMX8MQ_CLK_I2C1      = 144
     *
     * see `sddf/drivers/clk/imx/include/imx8mq-bindings.h` for more clock indices.
     * */

    uint32_t clk_id_to_enable = 196;
    ret = sddf_clk_enable(CLK_DRIVER_CH, clk_id_to_enable);
    if (ret) {
        sddf_dprintf("Failed to enable clock %u: err - %d\n", clk_id_to_enable, ret);
    } else {
        sddf_dprintf("Successfully enabled clock %u\n", clk_id_to_enable);
    }

    uint32_t clk_id_to_test_parent = 144;
    uint32_t parent_id = 0;
    ret = sddf_clk_get_parent(CLK_DRIVER_CH, clk_id_to_test_parent, &parent_id);
    if (ret) {
        sddf_dprintf("Failed to get the parent of clock %u: err - %d\n", clk_id_to_test_parent, ret);
    } else {
        sddf_dprintf("The parent of clock %u: %u\n", clk_id_to_test_parent, parent_id);
    }

    uint32_t pclk_idx = 3;
    ret = sddf_clk_set_parent(CLK_DRIVER_CH, clk_id_to_test_parent, pclk_idx);
    if (ret) {
        sddf_dprintf("Failed to set the parent of clock %u: err - %d\n", clk_id_to_test_parent, ret);
    } else {
        ret = sddf_clk_get_parent(CLK_DRIVER_CH, clk_id_to_test_parent, &parent_id);
        sddf_dprintf("The parent of clock %u has been set to: %u\n", clk_id_to_test_parent, parent_id);
    }

#else
    sddf_dprintf("No tests for the target board\n", ret);
#endif

    sddf_dprintf("--------------------\n");
}

void notified(microkit_channel ch)
{
}
