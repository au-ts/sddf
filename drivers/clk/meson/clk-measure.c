/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <clk-measure.h>
#include <clk-operations.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>

#define TIMER_CH 1

#define MSR_CLK_BASE 0x03300000
#define MSR_CLK_DUTY 0x00
#define MSR_CLK_REG0 0x01
#define MSR_CLK_REG1 0x02
#define MSR_CLK_REG2 0x03

#define DIV_ROUND_CLOSEST_ULL(x, divisor)(        \
{                                                 \
    typeof(divisor) __d = divisor;                \
    unsigned long long _tmp = (x) + (__d) / 2;    \
    do_div(_tmp, __d);                            \
    _tmp;                                         \
}                                                 \
)

static const char *const sm1_table[] = {
    [0] = "am_ring_osc_clk_out_ee[0]",
    [1] = "am_ring_osc_clk_out_ee[1]",
    [2] = "am_ring_osc_clk_out_ee[2]",
    [3] = "am_ring_osc_clk_out_ee[3]",
    [4] = "gp0_pll_clk",
    [5] = "gp1_pll_clk",
    [6] = "cts_enci_clk",
    [7] = "clk81",
    [8] = "cts_encp_clk",
    [9] = "cts_encl_clk",
    [10] = "cts_vdac_clk",
    [11] = "mac_eth_tx_clk",
    [12] = "hifi_pll_clk",
    [13] = "mod_tcon_clko",
    [14] = "cts_FEC_CLK_0",
    [15] = "cts_FEC_CLK_1",
    [16] = "cts_FEC_CLK_2",
    [17] = "sys_pll_div16",
    [18] = "sys_cpu_clk_div16",
    [19] = "lcd_an_clk_ph2",
    [20] = "rtc_osc_clk_out",
    [21] = "lcd_an_clk_ph3",
    [22] = "mac_eth_phy_ref_clk",
    [23] = "mpll_clk_50m",
    [24] = "cts_eth_clk125Mhz",
    [25] = "cts_eth_clk_rmii",
    [26] = "sc_clk_int",
    [27] = "co_clkin_to_mac",
    [28] = "cts_sar_adc_clk",
    [29] = "pcie_clk_inp",
    [30] = "pcie_clk_inn",
    [31] = "mpll_clk_test_out",
    [32] = "cts_vdec_clk",
    [33] = "1'b0",
    [34] = "eth_mppll_50m_ckout",
    [35] = "cts_mali_clk",
    [36] = "cts_hdmi_tx_pixel_clk",
    [37] = "cts_cdac_clk_c",
    [38] = "cts_vdin_meas_clk",
    [39] = "cts_bt656_clk0",
    [40] = "arm_ring_osc_clk_out[4]",
    [41] = "mac_eth_rx_clk_rmii",
    [42] = "mp0_clk_out",
    [43] = "fclk_div5",
    [44] = "cts_pwm_B_clk",
    [45] = "cts_pwm_A_clk",
    [46] = "cts_vpu_clk",
    [47] = "ddr_dpll_pt_clk",
    [48] = "mp1_clk_out",
    [49] = "mp2_clk_out",
    [50] = "mp3_clk_out",
    [51] = "cts_sd_emmc_clk_C",
    [52] = "cts_sd_emmc_clk_B",
    [53] = "cts_sd_emmc_clk_A",
    [54] = "cts_vpu_clkc",
    [55] = "vid_pll_div_clk_out",
    [56] = "cts_wave420l_aclk",
    [57] = "cts_wave420l_cclk",
    [58] = "cts_wave420l_bclk",
    [59] = "cts_hcodec_clk",
    [60] = "arm_ring_osc_clk_out[5]",
    [61] = "gpio_clk_msr",
    [62] = "cts_hevcb_clk",
    [63] = "cts_dsi_meas_clk",
    [64] = "cts_spicc_1_clk",
    [65] = "cts_spicc_0_clk",
    [66] = "cts_vid_lock_clk",
    [67] = "cts_dsi_phy_clk",
    [68] = "cts_hdcp22_esmclk",
    [69] = "cts_hdcp22_skpclk",
    [70] = "cts_pwm_F_clk",
    [71] = "cts_pwm_E_clk",
    [72] = "cts_pwm_D_clk",
    [73] = "cts_pwm_C_clk",
    [74] = "arm_ring_osc_clk_out[6]",
    [75] = "cts_hevcf_clk",
    [76] = "arm_ring_osc_clk_out[7]",
    [77] = "rng_ring_osc_clk[0]",
    [78] = "rng_ring_osc_clk[1]",
    [79] = "rng_ring_osc_clk[2]",
    [80] = "rng_ring_osc_clk[3]",
    [81] = "cts_vapbclk",
    [82] = "cts_ge2d_clk",
    [83] = "co_rx_clk",
    [84] = "co_tx_clk",
    [85] = "arm_ring_osc_clk_out[8]",
    [86] = "arm_ring_osc_clk_out[9]",
    [87] = "mipi_csi_phy_clk",
    [88] = "csi2_adapt_clk",
    [89] = "HDMI_CLK_TODIG",
    [90] = "cts_hdmitx_sys_clk",
    [91] = "nna_core_clk",
    [92] = "nna_axi_clk",
    [93] = "vad_clk",
    [94] = "eth_phy_rxclk",
    [95] = "eth_phy_plltxclk",
    [96] = "cts_vpu_clkb",
    [97] = "cts_vpu_clkb_tmp",
    [98] = "cts_ts_clk",
    [99] = "arm_ring_osc_clk_out[10]",
    [100] = "arm_ring_osc_clk_out[11]",
    [101] = "arm_ring_osc_clk_out[12]",
    [102] = "arm_ring_osc_clk_out[13]",
    [103] = "arm_ring_osc_clk_out[14]",
    [104] = "arm_ring_osc_clk_out[15]",
    [105] = "arm_ring_osc_clk_out[16]",
    [106] = "ephy_test_clk",
    [107] = "au_dac_clk_g128x",
    [108] = "c_alocker_in_clk",
    [109] = "c_alocker_out_clk",
    [110] = "audio_tdmout_c_sclk",
    [111] = "audio_tdmout_b_sclk",
    [112] = "audio_tdmout_a_sclk",
    [113] = "audio_tdmin_lb_sclk",
    [114] = "audio_tdmin_c_sclk",
    [115] = "audio_tdmin_b_sclk",
    [116] = "audio_tdmin_a_sclk",
    [117] = "audio_resampleA_clk",
    [118] = "audio_pdm_sysclk",
    [119] = "audio_spdifout_b_mst_clk",
    [120] = "audio_spdifout_mst_clk",
    [121] = "audio_spdifin_mst_clk",
    [122] = "mod_audio_pdm_dclk_o",
    [123] = "audio_resampled_clk",
    [124] = "earcx_pll_(dmac)_clk",
    [125] = "earcrx_pll_test_clk",
    [126] = "csi_phy0_clk_out",
    [127] = "clk_csi2_data",
};

unsigned long clk_msr(unsigned long clk_mux)
{
    volatile uint32_t *mclk_reg0 = ((void *)MSR_CLK_BASE + (MSR_CLK_REG0 << 2));
    volatile uint32_t *mclk_reg2 = ((void *)MSR_CLK_BASE + (MSR_CLK_REG2 << 2));
    uint32_t duration = 640;
    uint32_t regval = 0;

    /* Disable continuous measurement */
    /* Disable interrupts */
    *mclk_reg0 = regval;

    regval |= duration;               /* 64uS is enough for measure the frequence? */
    *mclk_reg0 = regval;

    regval |= (clk_mux << 20);        /* Select MUX */
    *mclk_reg0 = regval;

    regval |= (1 << 19);              /* enable the clock */
    regval |= (1 << 16);              /* enable measuring */
    *mclk_reg0 = regval;

    regval = *mclk_reg0;
    /* sddf_dprintf("reg_addr 0x%x, reg_val: 0x%0x\n", mclk_reg0, regval); */

    uint64_t start_time = sddf_timer_time_now(TIMER_CH);
    uint64_t now_time = start_time;

    /* TODO: Check the busy bit */
    /* if (regval & (1 << 31)) */
        /* sddf_dprintf("CLK | ERR: The clock measure logic is busy\n"); */

    /* Wait for the measurement to be done */
    while (true) {
        now_time = sddf_timer_time_now(TIMER_CH);

        if ((now_time - start_time) > 1000000) {
            break;
        }
        /* TODO: Could be optimised via timeouts */
        /* if (sleep_us) */
            /* udelay(sleep_us); */
    }

    regval &= ~(1 << 16);             /* disable measuring */
    *mclk_reg0 = regval;

    uint32_t msr_val = *mclk_reg2;

    return DIV_ROUND_CLOSEST_ULL((msr_val & ((1 << 19) - 1)) * 1000000ULL, duration);
}

int clk_msr_stat()
{
    unsigned long clk_freq;
    int i = 0;

    for (i = 0; i < 128; i++) {
        clk_freq = clk_msr(i);
        sddf_dprintf("[%4d][%4ld Hz] %s\n", i, clk_freq, sm1_table[i]);
    }

    return 0;
}
