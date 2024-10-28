// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright 2017-2018 NXP.
 *
 * Derived from: https://github.com/torvalds/linux/blob/75b607fab38d149f232f01eae5e6392b394dd659/drivers/clk/imx/clk-imx8mm.c
 */

#include <clk.h>
#include <utils.h>
#include <clk-imx8mq.h>
#include <clk-imx.h>
#include <sddf/util/util.h>
#include <clk-operations.h>
#include <sddf/util/printf.h>

#define CCM_BASE 0x30380000
#define CCM_ANALOG_BASE 0x30360000

static struct clk_parent_data pll_ref_sels[] = {
    { .name = "osc_25m", },
    { .name = "osc_27m", },
    { .name = "hdmi_phy_27m", },
    { .name = "dummy", },
};

static struct clk_parent_data arm_pll_bypass_sels[] = {
    { .name = "arm_pll", },
    { .name = "arm_pll_ref_sel", },
};

static struct clk_parent_data gpu_pll_bypass_sels[] = {
    { .name = "gpu_pll", },
    { .name = "gpu_pll_ref_sel", },
};

static struct clk_parent_data vpu_pll_bypass_sels[] = {
    { .name = "vpu_pll", },
    { .name = "vpu_pll_ref_sel", },
};

static struct clk_parent_data audio_pll1_bypass_sels[] = {
    { .name = "audio_pll1", },
    { .name = "audio_pll1_ref_sel", },
};

static struct clk_parent_data audio_pll2_bypass_sels[] = {
    { .name = "audio_pll2", },
    { .name = "audio_pll2_ref_sel", },
};

static struct clk_parent_data video_pll1_bypass_sels[] = {
    { .name = "video_pll1", },
    { .name = "video_pll1_ref_sel", },
};

static struct clk_parent_data sys3_pll_out_sels[] = {
    { .name = "sys3_pll1_ref_sel", },
};

static struct clk_parent_data dram_pll_out_sels[] = {
    { .name = "dram_pll1_ref_sel", },
};

static struct clk_parent_data video2_pll_out_sels[] = {
    { .name = "video2_pll1_ref_sel", },
};

static struct clk_parent_data imx8mq_a53_sels[] = {
    { .name = "osc_25m", },
    { .name = "arm_pll_out", },
    { .name = "sys2_pll_500m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys1_pll_400m", },
    { .name = "audio_pll1_out", },
    { .name = "sys3_pll_out", },
};

static struct clk_parent_data imx8mq_a53_core_sels[] = {
    { .name = "arm_a53_div", },
    { .name = "arm_pll_out", },
};

static struct clk_parent_data imx8mq_arm_m4_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys1_pll_800m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "sys3_pll_out", },
};

static struct clk_parent_data imx8mq_vpu_sels[] = {
    { .name = "osc_25m", },
    { .name = "arm_pll_out", },
    { .name = "sys2_pll_500m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys1_pll_400m", },
    { .name = "audio_pll1_out", },
    { .name = "vpu_pll_out", },
};

static struct clk_parent_data imx8mq_gpu_core_sels[] = {
    { .name = "osc_25m", },
    { .name = "gpu_pll_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_1000m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_gpu_shader_sels[] = {
    { .name = "osc_25m", },
    { .name = "gpu_pll_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_1000m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_main_axi_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_333m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys2_pll_1000m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_100m", },
};

static struct clk_parent_data imx8mq_enet_axi_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys2_pll_200m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "sys3_pll_out", },
};

static struct clk_parent_data imx8mq_nand_usdhc_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_133m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_250m", },
    { .name = "audio_pll1_out", },
};

static struct clk_parent_data imx8mq_vpu_bus_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "vpu_pll_out", },
    { .name = "audio_pll2_out", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_100m", },
};

static struct clk_parent_data imx8mq_disp_axi_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys1_pll_400m", },
    { .name = "audio_pll2_out", },
    { .name = "clk_ext1", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_disp_apb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys1_pll_40m", },
    { .name = "audio_pll2_out", },
    { .name = "clk_ext1", },
    { .name = "clk_ext3", },
};

static struct clk_parent_data imx8mq_disp_rtrm_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_400m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
};

static struct clk_parent_data imx8mq_usb_bus_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys2_pll_200m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext4", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_gpu_axi_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "gpu_pll_out", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_1000m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_gpu_ahb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "gpu_pll_out", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_1000m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_noc_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys2_pll_500m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_noc_apb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_333m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_800m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_ahb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_133m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_audio_ahb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys2_pll_166m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_dsi_ahb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_dram_alt_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys1_pll_100m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys1_pll_400m", },
    { .name = "audio_pll1_out", },
    { .name = "sys1_pll_266m", },
};

static struct clk_parent_data imx8mq_dram_apb_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_250m", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_vpu_g1_sels[] = {
    { .name = "osc_25m", },
    { .name = "vpu_pll_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys1_pll_100m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
};

static struct clk_parent_data imx8mq_vpu_g2_sels[] = {
    { .name = "osc_25m", },
    { .name = "vpu_pll_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys1_pll_100m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
};

static struct clk_parent_data imx8mq_disp_dtrc_sels[] = {
    { .name = "osc_25m", },
    { .name = "vpu_pll_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_disp_dc8000_sels[] = {
    { .name = "osc_25m", },
    { .name = "vpu_pll_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_pcie1_ctrl_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys2_pll_333m", },
    { .name = "sys3_pll_out", },
};

static struct clk_parent_data imx8mq_pcie1_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys2_pll_500m", },
    { .name = "clk_ext1", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_pcie1_aux_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_200m", },
};

static struct clk_parent_data imx8mq_dc_pixel_sels[] = {
    { .name = "osc_25m", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "audio_pll1_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_lcdif_pixel_sels[] = {
    { .name = "osc_25m", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "audio_pll1_out", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_sai1_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext1", },
    { .name = "clk_ext2", },
};

static struct clk_parent_data imx8mq_sai2_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
};

static struct clk_parent_data imx8mq_sai3_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext3", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_sai4_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext1", },
    { .name = "clk_ext2", },
};

static struct clk_parent_data imx8mq_sai5_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
};

static struct clk_parent_data imx8mq_sai6_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext3", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_spdif1_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
};

static struct clk_parent_data imx8mq_spdif2_sels[] = {
    { .name = "osc_25m", },
    { .name = "audio_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
    { .name = "sys1_pll_133m", },
    { .name = "osc_27m", },
    { .name = "clk_ext3", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_enet_ref_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_160m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "clk_ext4", },
};

static struct clk_parent_data imx8mq_enet_timer_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "audio_pll1_out", },
    { .name = "clk_ext1", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "clk_ext4", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_enet_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys2_pll_500m", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_nand_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_500m", },
    { .name = "audio_pll1_out", },
    { .name = "sys1_pll_400m", },
    { .name = "audio_pll2_out", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_250m", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_qspi_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_500m", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_266m", },
    { .name = "sys3_pll_out", },
    { .name = "sys1_pll_100m", },
};

static struct clk_parent_data imx8mq_usdhc1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys3_pll_out", },
    { .name = "sys1_pll_266m", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_100m", },
};

static struct clk_parent_data imx8mq_usdhc2_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys3_pll_out", },
    { .name = "sys1_pll_266m", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_100m", },
};

static struct clk_parent_data imx8mq_i2c1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_133m", },
};

static struct clk_parent_data imx8mq_i2c2_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_133m", },
};

static struct clk_parent_data imx8mq_i2c3_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_133m", },
};

static struct clk_parent_data imx8mq_i2c4_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "audio_pll2_out", },
    { .name = "sys1_pll_133m", },
};

static struct clk_parent_data imx8mq_uart1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext2", },
    { .name = "clk_ext4", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_uart2_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_uart3_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext2", },
    { .name = "clk_ext4", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_uart4_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_usb_core_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_100m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys2_pll_200m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_usb_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_100m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys2_pll_200m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_gic_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys2_pll_200m", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_ecspi1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_250m", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_ecspi2_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_250m", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_pwm1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext1", },
    { .name = "sys1_pll_80m", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_pwm2_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext1", },
    { .name = "sys1_pll_80m", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_pwm3_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext2", },
    { .name = "sys1_pll_80m", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_pwm4_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext2", },
    { .name = "sys1_pll_80m", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_gpt1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys1_pll_80m", },
    { .name = "audio_pll1_out", },
    { .name = "clk_ext1", },
};

static struct clk_parent_data imx8mq_wdog_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_133m", },
    { .name = "sys1_pll_160m", },
    { .name = "vpu_pll_out", },
    { .name = "sys2_pll_125m", },
    { .name = "sys3_pll_out", },
    { .name = "sys1_pll_80m", },
    { .name = "sys2_pll_166m", },
};

static struct clk_parent_data imx8mq_wrclk_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_40m", },
    { .name = "vpu_pll_out", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys1_pll_100m", },
};

static struct clk_parent_data imx8mq_dsi_core_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_dsi_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "clk_ext2", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_dsi_dbi_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_dsi_esc_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_csi1_core_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_csi1_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "clk_ext2", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_csi1_esc_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_csi2_core_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_csi2_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_125m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "clk_ext2", },
    { .name = "audio_pll2_out", },
    { .name = "video_pll1_out", },
};

static struct clk_parent_data imx8mq_csi2_esc_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_1000m", },
    { .name = "sys3_pll_out", },
    { .name = "clk_ext3", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_pcie2_ctrl_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_250m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_266m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys2_pll_500m", },
    { .name = "sys2_pll_333m", },
    { .name = "sys3_pll_out", },
};

static struct clk_parent_data imx8mq_pcie2_phy_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_100m", },
    { .name = "sys2_pll_500m", },
    { .name = "clk_ext1", },
    { .name = "clk_ext2", },
    { .name = "clk_ext3", },
    { .name = "clk_ext4", },
    { .name = "sys1_pll_400m", },
};

static struct clk_parent_data imx8mq_pcie2_aux_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys2_pll_50m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_100m", },
    { .name = "sys1_pll_80m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_200m", },
};

static struct clk_parent_data imx8mq_ecspi3_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_40m", },
    { .name = "sys1_pll_160m", },
    { .name = "sys1_pll_800m", },
    { .name = "sys3_pll_out", },
    { .name = "sys2_pll_250m", },
    { .name = "audio_pll2_out", },
};

static struct clk_parent_data imx8mq_dram_core_sels[] = {
    { .name = "dram_pll_out", },
    { .name = "dram_alt_root", },
};

static struct clk_parent_data imx8mq_clko1_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys1_pll_800m", },
    { .name = "osc_27m", },
    { .name = "sys1_pll_200m", },
    { .name = "audio_pll2_out", },
    { .name = "sys2_pll_500m", },
    { .name = "vpu_pll_out", },
    { .name = "sys1_pll_80m", },
};

static struct clk_parent_data imx8mq_clko2_sels[] = {
    { .name = "osc_25m", },
    { .name = "sys2_pll_200m", },
    { .name = "sys1_pll_400m", },
    { .name = "sys2_pll_166m", },
    { .name = "sys3_pll_out", },
    { .name = "audio_pll1_out", },
    { .name = "video_pll1_out", },
    { .name = "ckil", },
};

static struct clk_parent_data pllout_monitor_sels[] = {
    { .name = "osc_25m", },
    { .name = "osc_27m", },
    { .name = "dummy", },
    { .name = "dummy", },
    { .name = "ckil", },
    { .name = "audio_pll1_out_monitor", },
    { .name = "audio_pll2_out_monitor", },
    { .name = "video_pll1_out_monitor", },
    { .name = "gpu_pll_out_monitor", },
    { .name = "vpu_pll_out_monitor", },
    { .name = "arm_pll_out_monitor", },
    { .name = "sys_pll1_out_monitor", },
    { .name = "sys_pll2_out_monitor", },
    { .name = "sys_pll3_out_monitor", },
    { .name = "dram_pll_out_monitor", },
    { .name = "video_pll2_out_monitor", },
};


static IMX_CLK_SOURCE(dummy, 0);
static IMX_CLK_SOURCE(ckil, 0x8000);
static IMX_CLK_SOURCE(osc_25m, 0x17d7840);
static IMX_CLK_SOURCE(osc_27m, 0x19bfcc0);
static IMX_CLK_SOURCE(clk_ext1, 0x7ed6b40);
static IMX_CLK_SOURCE(clk_ext2, 0x7ed6b40);
static IMX_CLK_SOURCE(clk_ext3, 0x7ed6b40);
static IMX_CLK_SOURCE(clk_ext4, 0x7ed6b40);

static IMX_CLK_MUX(arm_pll_ref_sel, CCM_ANALOG_BASE, 0x28, 16, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(gpu_pll_ref_sel, CCM_ANALOG_BASE, 0x18, 16, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(vpu_pll_ref_sel, CCM_ANALOG_BASE, 0x20, 16, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(audio_pll1_ref_sel, CCM_ANALOG_BASE, 0x0, 16, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(audio_pll2_ref_sel, CCM_ANALOG_BASE, 0x8, 16, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(video_pll1_ref_sel, CCM_ANALOG_BASE, 0x10, 16, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(sys3_pll1_ref_sel, CCM_ANALOG_BASE, 0x48, 0, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(dram_pll1_ref_sel, CCM_ANALOG_BASE, 0x60, 0, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));
static IMX_CLK_MUX(video2_pll1_ref_sel, CCM_ANALOG_BASE, 0x54, 0, 2, pll_ref_sels, ARRAY_SIZE(pll_ref_sels));

static IMX_CLK_DIV(arm_pll_ref_div, { &arm_pll_ref_sel }, CCM_ANALOG_BASE, 0x28, 5, 6);
static IMX_CLK_DIV(gpu_pll_ref_div, { &gpu_pll_ref_sel }, CCM_ANALOG_BASE, 0x18, 5, 6);
static IMX_CLK_DIV(vpu_pll_ref_div, { &vpu_pll_ref_sel }, CCM_ANALOG_BASE, 0x20, 5, 6);
static IMX_CLK_DIV(audio_pll1_ref_div, { &audio_pll1_ref_sel }, CCM_ANALOG_BASE, 0x0, 5, 6);
static IMX_CLK_DIV(audio_pll2_ref_div, { &audio_pll2_ref_sel }, CCM_ANALOG_BASE, 0x8, 5, 6);
static IMX_CLK_DIV(video_pll1_ref_div, { &video_pll1_ref_sel }, CCM_ANALOG_BASE, 0x10, 5, 6);

static IMX_CLK_FRAC_PLL(arm_pll, { &arm_pll_ref_div }, CCM_ANALOG_BASE, 0x28);
static IMX_CLK_FRAC_PLL(gpu_pll, { &gpu_pll_ref_div }, CCM_ANALOG_BASE, 0x18);
static IMX_CLK_FRAC_PLL(vpu_pll, { &vpu_pll_ref_div }, CCM_ANALOG_BASE, 0x20);
static IMX_CLK_FRAC_PLL(audio_pll1, { &audio_pll1_ref_div }, CCM_ANALOG_BASE, 0x0);
static IMX_CLK_FRAC_PLL(audio_pll2, { &audio_pll2_ref_div }, CCM_ANALOG_BASE, 0x8);
static IMX_CLK_FRAC_PLL(video_pll1, { &video_pll1_ref_div }, CCM_ANALOG_BASE, 0x10);

/* PLL bypass out */
static IMX_CLK_MUX_FLAGS(arm_pll_bypass, CCM_ANALOG_BASE, 0x28, 14, 1, arm_pll_bypass_sels, ARRAY_SIZE(arm_pll_bypass_sels), CLK_SET_RATE_PARENT);
static IMX_CLK_MUX(gpu_pll_bypass, CCM_ANALOG_BASE, 0x18, 14, 1, gpu_pll_bypass_sels, ARRAY_SIZE(gpu_pll_bypass_sels));
static IMX_CLK_MUX(vpu_pll_bypass, CCM_ANALOG_BASE, 0x20, 14, 1, vpu_pll_bypass_sels, ARRAY_SIZE(vpu_pll_bypass_sels));
static IMX_CLK_MUX(audio_pll1_bypass, CCM_ANALOG_BASE, 0x0, 14, 1, audio_pll1_bypass_sels, ARRAY_SIZE(audio_pll1_bypass_sels));
static IMX_CLK_MUX(audio_pll2_bypass, CCM_ANALOG_BASE, 0x8, 14, 1, audio_pll2_bypass_sels, ARRAY_SIZE(audio_pll2_bypass_sels));
static IMX_CLK_MUX(video_pll1_bypass, CCM_ANALOG_BASE, 0x10, 14, 1, video_pll1_bypass_sels, ARRAY_SIZE(video_pll1_bypass_sels));

/* PLL OUT GATE */
static IMX_CLK_GATE(arm_pll_out, { &arm_pll_bypass }, CCM_ANALOG_BASE, 0x28, 21);
static IMX_CLK_GATE(gpu_pll_out, { &gpu_pll_bypass }, CCM_ANALOG_BASE, 0x18, 21);
static IMX_CLK_GATE(vpu_pll_out, { &vpu_pll_bypass }, CCM_ANALOG_BASE, 0x20, 21);
static IMX_CLK_GATE(audio_pll1_out, { &audio_pll1_bypass }, CCM_ANALOG_BASE, 0x0, 21);
static IMX_CLK_GATE(audio_pll2_out, { &audio_pll2_bypass }, CCM_ANALOG_BASE, 0x8, 21);
static IMX_CLK_GATE(video_pll1_out, { &video_pll1_bypass }, CCM_ANALOG_BASE, 0x10, 21);

static IMX_CLK_FIXED(sys1_pll_out, 800000000);
static IMX_CLK_FIXED(sys2_pll_out, 1000000000);
static IMX_CLK_SSCG_PLL(sys3_pll_out, sys3_pll_out_sels, ARRAY_SIZE(sys3_pll_out_sels), 0, 0, 0, CCM_ANALOG_BASE, 0x48, CLK_IS_CRITICAL);
static IMX_CLK_SSCG_PLL(dram_pll_out, dram_pll_out_sels, ARRAY_SIZE(dram_pll_out_sels), 0, 0, 0, CCM_ANALOG_BASE, 0x60, CLK_IS_CRITICAL | CLK_GET_RATE_NOCACHE);
static IMX_CLK_SSCG_PLL(video2_pll_out, video2_pll_out_sels, ARRAY_SIZE(video2_pll_out_sels), 0, 0, 0, CCM_ANALOG_BASE, 0x54, 0);

/* SYS PLL1 fixed output */
static IMX_CLK_FIXED_FACTOR(sys1_pll_40m, { &sys1_pll_out }, 1, 20);
static IMX_CLK_FIXED_FACTOR(sys1_pll_80m, { &sys1_pll_out }, 1, 10);
static IMX_CLK_FIXED_FACTOR(sys1_pll_100m, { &sys1_pll_out }, 1, 8);
static IMX_CLK_FIXED_FACTOR(sys1_pll_133m, { &sys1_pll_out }, 1, 6);
static IMX_CLK_FIXED_FACTOR(sys1_pll_160m, { &sys1_pll_out }, 1, 5);
static IMX_CLK_FIXED_FACTOR(sys1_pll_200m, { &sys1_pll_out }, 1, 4);
static IMX_CLK_FIXED_FACTOR(sys1_pll_266m, { &sys1_pll_out }, 1, 3);
static IMX_CLK_FIXED_FACTOR(sys1_pll_400m, { &sys1_pll_out }, 1, 2);
static IMX_CLK_FIXED_FACTOR(sys1_pll_800m, { &sys1_pll_out }, 1, 1);

/* SYS PLL2 fixed output */
static IMX_CLK_FIXED_FACTOR(sys2_pll_50m, { &sys2_pll_out }, 1, 20);
static IMX_CLK_FIXED_FACTOR(sys2_pll_100m, { &sys2_pll_out }, 1, 10);
static IMX_CLK_FIXED_FACTOR(sys2_pll_125m, { &sys2_pll_out }, 1, 8);
static IMX_CLK_FIXED_FACTOR(sys2_pll_166m, { &sys2_pll_out }, 1, 6);
static IMX_CLK_FIXED_FACTOR(sys2_pll_200m, { &sys2_pll_out }, 1, 5);
static IMX_CLK_FIXED_FACTOR(sys2_pll_250m, { &sys2_pll_out }, 1, 4);
static IMX_CLK_FIXED_FACTOR(sys2_pll_333m, { &sys2_pll_out }, 1, 3);
static IMX_CLK_FIXED_FACTOR(sys2_pll_500m, { &sys2_pll_out }, 1, 2);
static IMX_CLK_FIXED_FACTOR(sys2_pll_1000m, { &sys2_pll_out }, 1, 1);

static IMX_CLK_DIV(audio_pll1_out_monitor, { &audio_pll1_bypass }, CCM_ANALOG_BASE, 0x78, 0, 3);
static IMX_CLK_DIV(audio_pll2_out_monitor, { &audio_pll2_bypass }, CCM_ANALOG_BASE, 0x78, 4, 3);
static IMX_CLK_DIV(video_pll1_out_monitor, { &video_pll1_bypass }, CCM_ANALOG_BASE, 0x78, 8, 3);
static IMX_CLK_DIV(gpu_pll_out_monitor, { &gpu_pll_bypass }, CCM_ANALOG_BASE, 0x78, 12, 3);
static IMX_CLK_DIV(vpu_pll_out_monitor, { &vpu_pll_bypass }, CCM_ANALOG_BASE, 0x78, 16, 3);
static IMX_CLK_DIV(arm_pll_out_monitor, { &arm_pll_bypass }, CCM_ANALOG_BASE, 0x78, 20, 3);
static IMX_CLK_DIV(sys_pll1_out_monitor, { &sys1_pll_out }, CCM_ANALOG_BASE, 0x7c, 0, 3);
static IMX_CLK_DIV(sys_pll2_out_monitor, { &sys2_pll_out }, CCM_ANALOG_BASE, 0x7c, 4, 3);
static IMX_CLK_DIV(sys_pll3_out_monitor, { &sys3_pll_out }, CCM_ANALOG_BASE, 0x7c, 8, 3);
static IMX_CLK_DIV(dram_pll_out_monitor, { &dram_pll_out }, CCM_ANALOG_BASE, 0x7c, 12, 3);
static IMX_CLK_DIV(video_pll2_out_monitor, { &video2_pll_out }, CCM_ANALOG_BASE, 0x7c, 16, 3);
static IMX_CLK_MUX(pllout_monitor_sel, CCM_ANALOG_BASE, 0x74, 0, 4, pllout_monitor_sels, ARRAY_SIZE(pllout_monitor_sels));
static IMX_CLK_GATE(pllout_monitor_clk2, { &pllout_monitor_sel }, CCM_ANALOG_BASE, 0x74, 4);

/* CORE */
static IMX_CLK_COMPOSITE_CORE(arm_a53_div, imx8mq_a53_sels, CCM_BASE, 0x8000);

static IMX_CLK_COMPOSITE_CORE(arm_m4_core, imx8mq_arm_m4_sels, CCM_BASE, 0x8080);
static IMX_CLK_COMPOSITE_CORE(vpu_core, imx8mq_vpu_sels, CCM_BASE, 0x8100);
static IMX_CLK_COMPOSITE_CORE(gpu_core, imx8mq_gpu_core_sels, CCM_BASE, 0x8180);
static IMX_CLK_COMPOSITE(gpu_shader, imx8mq_gpu_shader_sels, CCM_BASE, 0x8200);

/* CORE SEL */
static IMX_CLK_MUX2(arm_a53_core, CCM_BASE, 0x9880, 24, 1, imx8mq_a53_core_sels, ARRAY_SIZE(imx8mq_a53_core_sels));

/* BUS */
static IMX_CLK_COMPOSITE_BUS(main_axi, imx8mq_main_axi_sels, CCM_BASE, 0x8800);
static IMX_CLK_COMPOSITE_BUS(enet_axi, imx8mq_enet_axi_sels, CCM_BASE, 0x8880);
static IMX_CLK_COMPOSITE_BUS(nand_usdhc_bus, imx8mq_nand_usdhc_sels, CCM_BASE, 0x8900);
static IMX_CLK_COMPOSITE_BUS(vpu_bus, imx8mq_vpu_bus_sels, CCM_BASE, 0x8980);
static IMX_CLK_COMPOSITE_BUS(disp_axi, imx8mq_disp_axi_sels, CCM_BASE, 0x8a00);
static IMX_CLK_COMPOSITE_BUS(disp_apb, imx8mq_disp_apb_sels, CCM_BASE, 0x8a80);
static IMX_CLK_COMPOSITE_BUS(disp_rtrm, imx8mq_disp_rtrm_sels, CCM_BASE, 0x8b00);
static IMX_CLK_COMPOSITE_BUS(usb_bus, imx8mq_usb_bus_sels, CCM_BASE, 0x8b80);
static IMX_CLK_COMPOSITE_BUS(gpu_axi, imx8mq_gpu_axi_sels, CCM_BASE, 0x8c00);
static IMX_CLK_COMPOSITE_BUS(gpu_ahb, imx8mq_gpu_ahb_sels, CCM_BASE, 0x8c80);
static IMX_CLK_COMPOSITE_BUS(noc, imx8mq_noc_sels, CCM_BASE, 0x8d00);
static IMX_CLK_COMPOSITE_BUS(noc_apb, imx8mq_noc_apb_sels, CCM_BASE, 0x8d80);

/* AHB */
/* AHB clock is used by the AHB bus therefore marked as critical */
static IMX_CLK_COMPOSITE_BUS(ahb, imx8mq_ahb_sels, CCM_BASE, 0x9000);
static IMX_CLK_COMPOSITE_BUS(audio_ahb, imx8mq_audio_ahb_sels, CCM_BASE, 0x9100);

/* IPG */
static IMX_CLK_DIV2(ipg_root, { &ahb }, CCM_BASE, 0x9080, 0, 1);
static IMX_CLK_DIV2(ipg_audio_root, { &audio_ahb }, CCM_BASE, 0x9180, 0, 1);

/*
 * DRAM clocks are manipulated from TF-A outside clock framework.
 * The fw_managed helper sets GET_RATE_NOCACHE and clears SET_PARENT_GATE
 * as div value should always be read from hardware
 */
static IMX_CLK_MUX2_FLAGS(dram_core_clk, CCM_BASE, 0x9800, 24, 1, imx8mq_dram_core_sels, ARRAY_SIZE(imx8mq_dram_core_sels), CLK_IS_CRITICAL);
static IMX_CLK_COMPOSITE_FW_MANAGED(dram_alt, imx8mq_dram_alt_sels, CCM_BASE, 0xa000);
static IMX_CLK_COMPOSITE_FW_MANAGED_CRITICAL(dram_apb, imx8mq_dram_apb_sels, CCM_BASE, 0xa080);

/* IP */
static IMX_CLK_COMPOSITE(vpu_g1, imx8mq_vpu_g1_sels,  CCM_BASE, 0xa100);
static IMX_CLK_COMPOSITE(vpu_g2, imx8mq_vpu_g2_sels,  CCM_BASE, 0xa180);
static IMX_CLK_COMPOSITE(disp_dtrc, imx8mq_disp_dtrc_sels,  CCM_BASE, 0xa200);
static IMX_CLK_COMPOSITE(disp_dc8000, imx8mq_disp_dc8000_sels,  CCM_BASE, 0xa280);
static IMX_CLK_COMPOSITE(pcie1_ctrl, imx8mq_pcie1_ctrl_sels,  CCM_BASE, 0xa300);
static IMX_CLK_COMPOSITE(pcie1_phy, imx8mq_pcie1_phy_sels,  CCM_BASE, 0xa380);
static IMX_CLK_COMPOSITE(pcie1_aux, imx8mq_pcie1_aux_sels,  CCM_BASE, 0xa400);
static IMX_CLK_COMPOSITE(dc_pixel, imx8mq_dc_pixel_sels,  CCM_BASE, 0xa480);
static IMX_CLK_COMPOSITE(lcdif_pixel, imx8mq_lcdif_pixel_sels,  CCM_BASE, 0xa500);
static IMX_CLK_COMPOSITE(sai1, imx8mq_sai1_sels,  CCM_BASE, 0xa580);
static IMX_CLK_COMPOSITE(sai2, imx8mq_sai2_sels,  CCM_BASE, 0xa600);
static IMX_CLK_COMPOSITE(sai3, imx8mq_sai3_sels,  CCM_BASE, 0xa680);
static IMX_CLK_COMPOSITE(sai4, imx8mq_sai4_sels,  CCM_BASE, 0xa700);
static IMX_CLK_COMPOSITE(sai5, imx8mq_sai5_sels,  CCM_BASE, 0xa780);
static IMX_CLK_COMPOSITE(sai6, imx8mq_sai6_sels,  CCM_BASE, 0xa800);
static IMX_CLK_COMPOSITE(spdif1, imx8mq_spdif1_sels,  CCM_BASE, 0xa880);
static IMX_CLK_COMPOSITE(spdif2, imx8mq_spdif2_sels,  CCM_BASE, 0xa900);
static IMX_CLK_COMPOSITE(enet_ref, imx8mq_enet_ref_sels,  CCM_BASE, 0xa980);
static IMX_CLK_COMPOSITE(enet_timer, imx8mq_enet_timer_sels,  CCM_BASE, 0xaa00);
static IMX_CLK_COMPOSITE(enet_phy, imx8mq_enet_phy_sels,  CCM_BASE, 0xaa80);
static IMX_CLK_COMPOSITE(nand, imx8mq_nand_sels,  CCM_BASE, 0xab00);
static IMX_CLK_COMPOSITE(qspi, imx8mq_qspi_sels,  CCM_BASE, 0xab80);
static IMX_CLK_COMPOSITE(usdhc1, imx8mq_usdhc1_sels,  CCM_BASE, 0xac00);
static IMX_CLK_COMPOSITE(usdhc2, imx8mq_usdhc2_sels,  CCM_BASE, 0xac80);
static IMX_CLK_COMPOSITE(i2c1, imx8mq_i2c1_sels,  CCM_BASE, 0xad00);
static IMX_CLK_COMPOSITE(i2c2, imx8mq_i2c2_sels,  CCM_BASE, 0xad80);
static IMX_CLK_COMPOSITE(i2c3, imx8mq_i2c3_sels,  CCM_BASE, 0xae00);
static IMX_CLK_COMPOSITE(i2c4, imx8mq_i2c4_sels,  CCM_BASE, 0xae80);
static IMX_CLK_COMPOSITE(uart1, imx8mq_uart1_sels,  CCM_BASE, 0xaf00);
static IMX_CLK_COMPOSITE(uart2, imx8mq_uart2_sels,  CCM_BASE, 0xaf80);
static IMX_CLK_COMPOSITE(uart3, imx8mq_uart3_sels,  CCM_BASE, 0xb000);
static IMX_CLK_COMPOSITE(uart4, imx8mq_uart4_sels,  CCM_BASE, 0xb080);
static IMX_CLK_COMPOSITE(usb_core_ref, imx8mq_usb_core_sels,  CCM_BASE, 0xb100);
static IMX_CLK_COMPOSITE(usb_phy_ref, imx8mq_usb_phy_sels,  CCM_BASE, 0xb180);
static IMX_CLK_COMPOSITE(gic, imx8mq_gic_sels,  CCM_BASE, 0xb200);
static IMX_CLK_COMPOSITE(ecspi1, imx8mq_ecspi1_sels,  CCM_BASE, 0xb280);
static IMX_CLK_COMPOSITE(ecspi2, imx8mq_ecspi2_sels,  CCM_BASE, 0xb300);
static IMX_CLK_COMPOSITE(pwm1, imx8mq_pwm1_sels,  CCM_BASE, 0xb380);
static IMX_CLK_COMPOSITE(pwm2, imx8mq_pwm2_sels,  CCM_BASE, 0xb400);
static IMX_CLK_COMPOSITE(pwm3, imx8mq_pwm3_sels,  CCM_BASE, 0xb480);
static IMX_CLK_COMPOSITE(pwm4, imx8mq_pwm4_sels,  CCM_BASE, 0xb500);
static IMX_CLK_COMPOSITE(gpt1, imx8mq_gpt1_sels,  CCM_BASE, 0xb580);
static IMX_CLK_COMPOSITE(wdog, imx8mq_wdog_sels,  CCM_BASE, 0xb900);
static IMX_CLK_COMPOSITE(wrclk, imx8mq_wrclk_sels,  CCM_BASE, 0xb980);
static IMX_CLK_COMPOSITE(clko1, imx8mq_clko1_sels,  CCM_BASE, 0xba00);
static IMX_CLK_COMPOSITE(clko2, imx8mq_clko2_sels,  CCM_BASE, 0xba80);
static IMX_CLK_COMPOSITE(dsi_core, imx8mq_dsi_core_sels,  CCM_BASE, 0xbb00);
static IMX_CLK_COMPOSITE(dsi_phy_ref, imx8mq_dsi_phy_sels,  CCM_BASE, 0xbb80);
static IMX_CLK_COMPOSITE(dsi_dbi, imx8mq_dsi_dbi_sels,  CCM_BASE, 0xbc00);
static IMX_CLK_COMPOSITE(dsi_esc, imx8mq_dsi_esc_sels,  CCM_BASE, 0xbc80);
static IMX_CLK_COMPOSITE(dsi_ahb, imx8mq_dsi_ahb_sels,  CCM_BASE, 0x9200);
static IMX_CLK_DIV2(dsi_ipg_div, { &dsi_ahb },  CCM_BASE, 0x9280, 0, 6);
static IMX_CLK_COMPOSITE(csi1_core, imx8mq_csi1_core_sels,  CCM_BASE, 0xbd00);
static IMX_CLK_COMPOSITE(csi1_phy_ref, imx8mq_csi1_phy_sels,  CCM_BASE, 0xbd80);
static IMX_CLK_COMPOSITE(csi1_esc, imx8mq_csi1_esc_sels,  CCM_BASE, 0xbe00);
static IMX_CLK_COMPOSITE(csi2_core, imx8mq_csi2_core_sels,  CCM_BASE, 0xbe80);
static IMX_CLK_COMPOSITE(csi2_phy_ref, imx8mq_csi2_phy_sels,  CCM_BASE, 0xbf00);
static IMX_CLK_COMPOSITE(csi2_esc, imx8mq_csi2_esc_sels,  CCM_BASE, 0xbf80);
static IMX_CLK_COMPOSITE(pcie2_ctrl, imx8mq_pcie2_ctrl_sels,  CCM_BASE, 0xc000);
static IMX_CLK_COMPOSITE(pcie2_phy, imx8mq_pcie2_phy_sels,  CCM_BASE, 0xc080);
static IMX_CLK_COMPOSITE(pcie2_aux, imx8mq_pcie2_aux_sels,  CCM_BASE, 0xc100);
static IMX_CLK_COMPOSITE(ecspi3, imx8mq_ecspi3_sels,  CCM_BASE, 0xc180);

static IMX_CLK_GATE4(ecspi1_root_clk, { &ecspi1 }, CCM_BASE, 0x4070, 0);
static IMX_CLK_GATE4(ecspi2_root_clk, { &ecspi2 }, CCM_BASE, 0x4080, 0);
static IMX_CLK_GATE4(ecspi3_root_clk, { &ecspi3 }, CCM_BASE, 0x4090, 0);
static IMX_CLK_GATE4(enet1_root_clk, { &enet_axi }, CCM_BASE, 0x40a0, 0);
static IMX_CLK_GATE4(gpio1_root_clk, { &ipg_root }, CCM_BASE, 0x40b0, 0);
static IMX_CLK_GATE4(gpio2_root_clk, { &ipg_root }, CCM_BASE, 0x40c0, 0);
static IMX_CLK_GATE4(gpio3_root_clk, { &ipg_root }, CCM_BASE, 0x40d0, 0);
static IMX_CLK_GATE4(gpio4_root_clk, { &ipg_root }, CCM_BASE, 0x40e0, 0);
static IMX_CLK_GATE4(gpio5_root_clk, { &ipg_root }, CCM_BASE, 0x40f0, 0);
static IMX_CLK_GATE4(gpt1_root_clk, { &gpt1 }, CCM_BASE, 0x4100, 0);
static IMX_CLK_GATE4(i2c1_root_clk, { &i2c1 }, CCM_BASE, 0x4170, 0);
static IMX_CLK_GATE4(i2c2_root_clk, { &i2c2 }, CCM_BASE, 0x4180, 0);
static IMX_CLK_GATE4(i2c3_root_clk, { &i2c3 }, CCM_BASE, 0x4190, 0);
static IMX_CLK_GATE4(i2c4_root_clk, { &i2c4 }, CCM_BASE, 0x41a0, 0);
static IMX_CLK_GATE4(mu_root_clk, { &ipg_root }, CCM_BASE, 0x4210, 0);
static IMX_CLK_GATE4(ocotp_root_clk, { &ipg_root }, CCM_BASE, 0x4220, 0);
static IMX_CLK_GATE4(pcie1_root_clk, { &pcie1_ctrl }, CCM_BASE, 0x4250, 0);
static IMX_CLK_GATE4(pcie2_root_clk, { &pcie2_ctrl }, CCM_BASE, 0x4640, 0);
static IMX_CLK_GATE4(pwm1_root_clk, { &pwm1 }, CCM_BASE, 0x4280, 0);
static IMX_CLK_GATE4(pwm2_root_clk, { &pwm2 }, CCM_BASE, 0x4290, 0);
static IMX_CLK_GATE4(pwm3_root_clk, { &pwm3 }, CCM_BASE, 0x42a0, 0);
static IMX_CLK_GATE4(pwm4_root_clk, { &pwm4 }, CCM_BASE, 0x42b0, 0);
static IMX_CLK_GATE4(qspi_root_clk, { &qspi }, CCM_BASE, 0x42f0, 0);

static IMX_CLK_GATE2_SHARED2(nand_root_clk, { &nand }, CCM_BASE, 0x4300, 0, &share_count_nand);
static IMX_CLK_GATE2_SHARED2(nand_usdhc_rawnand_clk, { &nand_usdhc_bus }, CCM_BASE, 0x4300, 0, &share_count_nand);
static IMX_CLK_GATE2_SHARED2(sai1_root_clk, { &sai1 }, CCM_BASE, 0x4330, 0, &share_count_sai1);
static IMX_CLK_GATE2_SHARED2(sai1_ipg_clk, { &ipg_audio_root }, CCM_BASE, 0x4330, 0, &share_count_sai1);
static IMX_CLK_GATE2_SHARED2(sai2_root_clk, { &sai2 }, CCM_BASE, 0x4340, 0, &share_count_sai2);
static IMX_CLK_GATE2_SHARED2(sai2_ipg_clk, { &ipg_root }, CCM_BASE, 0x4340, 0, &share_count_sai2);
static IMX_CLK_GATE2_SHARED2(sai3_root_clk, { &sai3 }, CCM_BASE, 0x4350, 0, &share_count_sai3);
static IMX_CLK_GATE2_SHARED2(sai3_ipg_clk, { &ipg_root }, CCM_BASE, 0x4350, 0, &share_count_sai3);
static IMX_CLK_GATE2_SHARED2(sai4_root_clk, { &sai4 }, CCM_BASE, 0x4360, 0, &share_count_sai4);
static IMX_CLK_GATE2_SHARED2(sai4_ipg_clk, { &ipg_audio_root }, CCM_BASE, 0x4360, 0, &share_count_sai4);
static IMX_CLK_GATE2_SHARED2(sai5_root_clk, { &sai5 }, CCM_BASE, 0x4370, 0, &share_count_sai5);
static IMX_CLK_GATE2_SHARED2(sai5_ipg_clk, { &ipg_audio_root }, CCM_BASE, 0x4370, 0, &share_count_sai5);
static IMX_CLK_GATE2_SHARED2(sai6_root_clk, { &sai6 }, CCM_BASE, 0x4380, 0, &share_count_sai6);
static IMX_CLK_GATE2_SHARED2(sai6_ipg_clk, { &ipg_audio_root }, CCM_BASE, 0x4380, 0, &share_count_sai6);
static IMX_CLK_GATE4(uart1_root_clk, { &uart1 }, CCM_BASE, 0x4490, 0);
static IMX_CLK_GATE4(uart2_root_clk, { &uart2 }, CCM_BASE, 0x44a0, 0);
static IMX_CLK_GATE4(uart3_root_clk, { &uart3 }, CCM_BASE, 0x44b0, 0);
static IMX_CLK_GATE4(uart4_root_clk, { &uart4 }, CCM_BASE, 0x44c0, 0);
static IMX_CLK_GATE4(usb1_ctrl_root_clk, { &usb_bus }, CCM_BASE, 0x44d0, 0);
static IMX_CLK_GATE4(usb2_ctrl_root_clk, { &usb_bus }, CCM_BASE, 0x44e0, 0);
static IMX_CLK_GATE4(usb1_phy_root_clk, { &usb_phy_ref }, CCM_BASE, 0x44f0, 0);
static IMX_CLK_GATE4(usb2_phy_root_clk, { &usb_phy_ref }, CCM_BASE, 0x4500, 0);
static IMX_CLK_GATE4(usdhc1_root_clk, { &usdhc1 }, CCM_BASE, 0x4510, 0);
static IMX_CLK_GATE4(usdhc2_root_clk, { &usdhc2 }, CCM_BASE, 0x4520, 0);
static IMX_CLK_GATE4(wdog1_root_clk, { &wdog }, CCM_BASE, 0x4530, 0);
static IMX_CLK_GATE4(wdog2_root_clk, { &wdog }, CCM_BASE, 0x4540, 0);
static IMX_CLK_GATE4(wdog3_root_clk, { &wdog }, CCM_BASE, 0x4550, 0);
static IMX_CLK_GATE2_FLAGS(vpu_g1_root_clk, { &vpu_g1 }, CCM_BASE, 0x4560, 0, CLK_SET_RATE_PARENT | CLK_OPS_PARENT_ENABLE);
static IMX_CLK_GATE4(gpu_root_clk, { &gpu_core }, CCM_BASE, 0x4570, 0);
static IMX_CLK_GATE2_FLAGS(vpu_g2_root_clk, { &vpu_g2 }, CCM_BASE, 0x45a0, 0, CLK_SET_RATE_PARENT | CLK_OPS_PARENT_ENABLE);
static IMX_CLK_GATE2_SHARED2(disp_root_clk, { &disp_dc8000 }, CCM_BASE, 0x45d0, 0, &share_count_dcss);
static IMX_CLK_GATE2_SHARED2(disp_axi_root_clk, { &disp_axi }, CCM_BASE, 0x45d0, 0, &share_count_dcss);
static IMX_CLK_GATE2_SHARED2(disp_apb_root_clk, { &disp_apb }, CCM_BASE, 0x45d0, 0, &share_count_dcss);
static IMX_CLK_GATE2_SHARED2(disp_rtrm_root_clk, { &disp_rtrm }, CCM_BASE, 0x45d0, 0, &share_count_dcss);
static IMX_CLK_GATE4(tmu_root_clk, { &ipg_root }, CCM_BASE, 0x4620, 0);
static IMX_CLK_GATE2_FLAGS(vpu_dec_root_clk, { &vpu_bus }, CCM_BASE, 0x4630, 0, CLK_SET_RATE_PARENT | CLK_OPS_PARENT_ENABLE);
static IMX_CLK_GATE4(csi1_root_clk, { &csi1_core }, CCM_BASE, 0x4650, 0);
static IMX_CLK_GATE4(csi2_root_clk, { &csi2_core }, CCM_BASE, 0x4660, 0);
static IMX_CLK_GATE4(sdma1_clk, { &ipg_root }, CCM_BASE, 0x43a0, 0);
static IMX_CLK_GATE4(sdma2_clk, { &ipg_audio_root }, CCM_BASE, 0x43b0, 0);

static struct clk *imx8mq_clks[] = {
    [IMX8MQ_CLK_DUMMY]              = &dummy,
    [IMX8MQ_CLK_32K]                = &ckil,
    [IMX8MQ_CLK_25M]                = &osc_25m,
    [IMX8MQ_CLK_27M]                = &osc_27m,
    [IMX8MQ_CLK_EXT1]               = &clk_ext1,
    [IMX8MQ_CLK_EXT2]               = &clk_ext2,
    [IMX8MQ_CLK_EXT3]               = &clk_ext3,
    [IMX8MQ_CLK_EXT4]               = &clk_ext4,
    [IMX8MQ_ARM_PLL_REF_SEL]        = &arm_pll_ref_sel,
    [IMX8MQ_GPU_PLL_REF_SEL]        = &gpu_pll_ref_sel,
    [IMX8MQ_VPU_PLL_REF_SEL]        = &vpu_pll_ref_sel,
    [IMX8MQ_AUDIO_PLL1_REF_SEL]     = &audio_pll1_ref_sel,
    [IMX8MQ_AUDIO_PLL2_REF_SEL]     = &audio_pll2_ref_sel,
    [IMX8MQ_VIDEO_PLL1_REF_SEL]     = &video_pll1_ref_sel,
    [IMX8MQ_SYS3_PLL1_REF_SEL]      = &sys3_pll1_ref_sel,
    [IMX8MQ_DRAM_PLL1_REF_SEL]      = &dram_pll1_ref_sel,
    [IMX8MQ_VIDEO2_PLL1_REF_SEL]    = &video2_pll1_ref_sel,
    [IMX8MQ_ARM_PLL_REF_DIV]        = &arm_pll_ref_div,
    [IMX8MQ_GPU_PLL_REF_DIV]        = &gpu_pll_ref_div,
    [IMX8MQ_VPU_PLL_REF_DIV]        = &vpu_pll_ref_div,
    [IMX8MQ_AUDIO_PLL1_REF_DIV]     = &audio_pll1_ref_div,
    [IMX8MQ_AUDIO_PLL2_REF_DIV]     = &audio_pll2_ref_div,
    [IMX8MQ_VIDEO_PLL1_REF_DIV]     = &video_pll1_ref_div,
    [IMX8MQ_ARM_PLL]                = &arm_pll,
    [IMX8MQ_GPU_PLL]                = &gpu_pll,
    [IMX8MQ_VPU_PLL]                = &vpu_pll,
    [IMX8MQ_AUDIO_PLL1]             = &audio_pll1,
    [IMX8MQ_AUDIO_PLL2]             = &audio_pll2,
    [IMX8MQ_VIDEO_PLL1]             = &video_pll1,
    [IMX8MQ_ARM_PLL_BYPASS]         = &arm_pll_bypass,
    [IMX8MQ_GPU_PLL_BYPASS]         = &gpu_pll_bypass,
    [IMX8MQ_VPU_PLL_BYPASS]         = &vpu_pll_bypass,
    [IMX8MQ_AUDIO_PLL1_BYPASS]      = &audio_pll1_bypass,
    [IMX8MQ_AUDIO_PLL2_BYPASS]      = &audio_pll2_bypass,
    [IMX8MQ_VIDEO_PLL1_BYPASS]      = &video_pll1_bypass,
    [IMX8MQ_ARM_PLL_OUT]            = &arm_pll_out,
    [IMX8MQ_GPU_PLL_OUT]            = &gpu_pll_out,
    [IMX8MQ_VPU_PLL_OUT]            = &vpu_pll_out,
    [IMX8MQ_AUDIO_PLL1_OUT]         = &audio_pll1_out,
    [IMX8MQ_AUDIO_PLL2_OUT]         = &audio_pll2_out,
    [IMX8MQ_VIDEO_PLL1_OUT]         = &video_pll1_out,
    [IMX8MQ_SYS1_PLL_OUT]           = &sys1_pll_out,
    [IMX8MQ_SYS2_PLL_OUT]           = &sys2_pll_out,
    [IMX8MQ_SYS3_PLL_OUT]           = &sys3_pll_out,
    [IMX8MQ_DRAM_PLL_OUT]           = &dram_pll_out,
    [IMX8MQ_VIDEO2_PLL_OUT]         = &video2_pll_out,
    [IMX8MQ_SYS1_PLL_40M]           = &sys1_pll_40m,
    [IMX8MQ_SYS1_PLL_80M]           = &sys1_pll_80m,
    [IMX8MQ_SYS1_PLL_100M]          = &sys1_pll_100m,
    [IMX8MQ_SYS1_PLL_133M]          = &sys1_pll_133m,
    [IMX8MQ_SYS1_PLL_160M]          = &sys1_pll_160m,
    [IMX8MQ_SYS1_PLL_200M]          = &sys1_pll_200m,
    [IMX8MQ_SYS1_PLL_266M]          = &sys1_pll_266m,
    [IMX8MQ_SYS1_PLL_400M]          = &sys1_pll_400m,
    [IMX8MQ_SYS1_PLL_800M]          = &sys1_pll_800m,
    [IMX8MQ_SYS2_PLL_50M]           = &sys2_pll_50m,
    [IMX8MQ_SYS2_PLL_100M]          = &sys2_pll_100m,
    [IMX8MQ_SYS2_PLL_125M]          = &sys2_pll_125m,
    [IMX8MQ_SYS2_PLL_166M]          = &sys2_pll_166m,
    [IMX8MQ_SYS2_PLL_200M]          = &sys2_pll_200m,
    [IMX8MQ_SYS2_PLL_250M]          = &sys2_pll_250m,
    [IMX8MQ_SYS2_PLL_333M]          = &sys2_pll_333m,
    [IMX8MQ_SYS2_PLL_500M]          = &sys2_pll_500m,
    [IMX8MQ_SYS2_PLL_1000M]         = &sys2_pll_1000m,
    [IMX8MQ_CLK_MON_AUDIO_PLL1_DIV] = &audio_pll1_out_monitor,
    [IMX8MQ_CLK_MON_AUDIO_PLL2_DIV] = &audio_pll2_out_monitor,
    [IMX8MQ_CLK_MON_VIDEO_PLL1_DIV] = &video_pll1_out_monitor,
    [IMX8MQ_CLK_MON_GPU_PLL_DIV]    = &gpu_pll_out_monitor,
    [IMX8MQ_CLK_MON_VPU_PLL_DIV]    = &vpu_pll_out_monitor,
    [IMX8MQ_CLK_MON_ARM_PLL_DIV]    = &arm_pll_out_monitor,
    [IMX8MQ_CLK_MON_SYS_PLL1_DIV]   = &sys_pll1_out_monitor,
    [IMX8MQ_CLK_MON_SYS_PLL2_DIV]   = &sys_pll2_out_monitor,
    [IMX8MQ_CLK_MON_SYS_PLL3_DIV]   = &sys_pll3_out_monitor,
    [IMX8MQ_CLK_MON_DRAM_PLL_DIV]   = &dram_pll_out_monitor,
    [IMX8MQ_CLK_MON_VIDEO_PLL2_DIV] = &video_pll2_out_monitor,
    [IMX8MQ_CLK_MON_SEL]            = &pllout_monitor_sel,
    [IMX8MQ_CLK_MON_CLK2_OUT]       = &pllout_monitor_clk2,
    [IMX8MQ_CLK_A53_DIV]            = &arm_a53_div,
    [IMX8MQ_CLK_A53_CG]             = &arm_a53_div,
    [IMX8MQ_CLK_A53_SRC]            = &arm_a53_div,
    [IMX8MQ_CLK_M4_CORE]            = &arm_m4_core,
    [IMX8MQ_CLK_VPU_CORE]           = &vpu_core,
    [IMX8MQ_CLK_GPU_CORE]           = &gpu_core,
    [IMX8MQ_CLK_GPU_SHADER]         = &gpu_shader,
    [IMX8MQ_CLK_M4_SRC]             = &arm_m4_core,
    [IMX8MQ_CLK_M4_CG]              = &arm_m4_core,
    [IMX8MQ_CLK_M4_DIV]             = &arm_m4_core,
    [IMX8MQ_CLK_VPU_SRC]            = &vpu_core,
    [IMX8MQ_CLK_VPU_CG]             = &vpu_core,
    [IMX8MQ_CLK_VPU_DIV]            = &vpu_core,
    [IMX8MQ_CLK_GPU_CORE_SRC]       = &gpu_core,
    [IMX8MQ_CLK_GPU_CORE_CG]        = &gpu_core,
    [IMX8MQ_CLK_GPU_CORE_DIV]       = &gpu_core,
    [IMX8MQ_CLK_GPU_SHADER_SRC]     = &gpu_shader,
    [IMX8MQ_CLK_GPU_SHADER_CG]      = &gpu_shader,
    [IMX8MQ_CLK_GPU_SHADER_DIV]     = &gpu_shader,
    [IMX8MQ_CLK_A53_CORE]           = &arm_a53_core,
    [IMX8MQ_CLK_MAIN_AXI]           = &main_axi,
    [IMX8MQ_CLK_ENET_AXI]           = &enet_axi,
    [IMX8MQ_CLK_NAND_USDHC_BUS]     = &nand_usdhc_bus,
    [IMX8MQ_CLK_VPU_BUS]            = &vpu_bus,
    [IMX8MQ_CLK_DISP_AXI]           = &disp_axi,
    [IMX8MQ_CLK_DISP_APB]           = &disp_apb,
    [IMX8MQ_CLK_DISP_RTRM]          = &disp_rtrm,
    [IMX8MQ_CLK_USB_BUS]            = &usb_bus,
    [IMX8MQ_CLK_GPU_AXI]            = &gpu_axi,
    [IMX8MQ_CLK_GPU_AHB]            = &gpu_ahb,
    [IMX8MQ_CLK_NOC]                = &noc,
    [IMX8MQ_CLK_NOC_APB]            = &noc_apb,
    [IMX8MQ_CLK_AHB]                = &ahb,
    [IMX8MQ_CLK_AUDIO_AHB]          = &audio_ahb,
    [IMX8MQ_CLK_IPG_ROOT]           = &ipg_root,
    [IMX8MQ_CLK_IPG_AUDIO_ROOT]     = &ipg_audio_root,
    [IMX8MQ_CLK_DRAM_CORE]          = &dram_core_clk,
    [IMX8MQ_CLK_DRAM_ALT]           = &dram_alt,
    [IMX8MQ_CLK_DRAM_APB]           = &dram_apb,
    [IMX8MQ_CLK_VPU_G1]             = &vpu_g1,
    [IMX8MQ_CLK_VPU_G2]             = &vpu_g2,
    [IMX8MQ_CLK_DISP_DTRC]          = &disp_dtrc,
    [IMX8MQ_CLK_DISP_DC8000]        = &disp_dc8000,
    [IMX8MQ_CLK_PCIE1_CTRL]         = &pcie1_ctrl,
    [IMX8MQ_CLK_PCIE1_PHY]          = &pcie1_phy,
    [IMX8MQ_CLK_PCIE1_AUX]          = &pcie1_aux,
    [IMX8MQ_CLK_DC_PIXEL]           = &dc_pixel,
    [IMX8MQ_CLK_LCDIF_PIXEL]        = &lcdif_pixel,
    [IMX8MQ_CLK_SAI1]               = &sai1,
    [IMX8MQ_CLK_SAI2]               = &sai2,
    [IMX8MQ_CLK_SAI3]               = &sai3,
    [IMX8MQ_CLK_SAI4]               = &sai4,
    [IMX8MQ_CLK_SAI5]               = &sai5,
    [IMX8MQ_CLK_SAI6]               = &sai6,
    [IMX8MQ_CLK_SPDIF1]             = &spdif1,
    [IMX8MQ_CLK_SPDIF2]             = &spdif2,
    [IMX8MQ_CLK_ENET_REF]           = &enet_ref,
    [IMX8MQ_CLK_ENET_TIMER]         = &enet_timer,
    [IMX8MQ_CLK_ENET_PHY_REF]       = &enet_phy,
    [IMX8MQ_CLK_NAND]               = &nand,
    [IMX8MQ_CLK_QSPI]               = &qspi,
    [IMX8MQ_CLK_USDHC1]             = &usdhc1,
    [IMX8MQ_CLK_USDHC2]             = &usdhc2,
    [IMX8MQ_CLK_I2C1]               = &i2c1,
    [IMX8MQ_CLK_I2C2]               = &i2c2,
    [IMX8MQ_CLK_I2C3]               = &i2c3,
    [IMX8MQ_CLK_I2C4]               = &i2c4,
    [IMX8MQ_CLK_UART1]              = &uart1,
    [IMX8MQ_CLK_UART2]              = &uart2,
    [IMX8MQ_CLK_UART3]              = &uart3,
    [IMX8MQ_CLK_UART4]              = &uart4,
    [IMX8MQ_CLK_USB_CORE_REF]       = &usb_core_ref,
    [IMX8MQ_CLK_USB_PHY_REF]        = &usb_phy_ref,
    [IMX8MQ_CLK_GIC]                = &gic,
    [IMX8MQ_CLK_ECSPI1]             = &ecspi1,
    [IMX8MQ_CLK_ECSPI2]             = &ecspi2,
    [IMX8MQ_CLK_PWM1]               = &pwm1,
    [IMX8MQ_CLK_PWM2]               = &pwm2,
    [IMX8MQ_CLK_PWM3]               = &pwm3,
    [IMX8MQ_CLK_PWM4]               = &pwm4,
    [IMX8MQ_CLK_GPT1]               = &gpt1,
    [IMX8MQ_CLK_WDOG]               = &wdog,
    [IMX8MQ_CLK_WRCLK]              = &wrclk,
    [IMX8MQ_CLK_CLKO1]              = &clko1,
    [IMX8MQ_CLK_CLKO2]              = &clko2,
    [IMX8MQ_CLK_DSI_CORE]           = &dsi_core,
    [IMX8MQ_CLK_DSI_PHY_REF]        = &dsi_phy_ref,
    [IMX8MQ_CLK_DSI_DBI]            = &dsi_dbi,
    [IMX8MQ_CLK_DSI_ESC]            = &dsi_esc,
    [IMX8MQ_CLK_DSI_AHB]            = &dsi_ahb,
    [IMX8MQ_CLK_DSI_IPG_DIV]        = &dsi_ipg_div,
    [IMX8MQ_CLK_CSI1_CORE]          = &csi1_core,
    [IMX8MQ_CLK_CSI1_PHY_REF]       = &csi1_phy_ref,
    [IMX8MQ_CLK_CSI1_ESC]           = &csi1_esc,
    [IMX8MQ_CLK_CSI2_CORE]          = &csi2_core,
    [IMX8MQ_CLK_CSI2_PHY_REF]       = &csi2_phy_ref,
    [IMX8MQ_CLK_CSI2_ESC]           = &csi2_esc,
    [IMX8MQ_CLK_PCIE2_CTRL]         = &pcie2_ctrl,
    [IMX8MQ_CLK_PCIE2_PHY]          = &pcie2_phy,
    [IMX8MQ_CLK_PCIE2_AUX]          = &pcie2_aux,
    [IMX8MQ_CLK_ECSPI3]             = &ecspi3,
    [IMX8MQ_CLK_ECSPI1_ROOT]        = &ecspi1_root_clk,
    [IMX8MQ_CLK_ECSPI2_ROOT]        = &ecspi2_root_clk,
    [IMX8MQ_CLK_ECSPI3_ROOT]        = &ecspi3_root_clk,
    [IMX8MQ_CLK_ENET1_ROOT]         = &enet1_root_clk,
    [IMX8MQ_CLK_GPIO1_ROOT]         = &gpio1_root_clk,
    [IMX8MQ_CLK_GPIO2_ROOT]         = &gpio2_root_clk,
    [IMX8MQ_CLK_GPIO3_ROOT]         = &gpio3_root_clk,
    [IMX8MQ_CLK_GPIO4_ROOT]         = &gpio4_root_clk,
    [IMX8MQ_CLK_GPIO5_ROOT]         = &gpio5_root_clk,
    [IMX8MQ_CLK_GPT1_ROOT]          = &gpt1_root_clk,
    [IMX8MQ_CLK_I2C1_ROOT]          = &i2c1_root_clk,
    [IMX8MQ_CLK_I2C2_ROOT]          = &i2c2_root_clk,
    [IMX8MQ_CLK_I2C3_ROOT]          = &i2c3_root_clk,
    [IMX8MQ_CLK_I2C4_ROOT]          = &i2c4_root_clk,
    [IMX8MQ_CLK_MU_ROOT]            = &mu_root_clk,
    [IMX8MQ_CLK_OCOTP_ROOT]         = &ocotp_root_clk,
    [IMX8MQ_CLK_PCIE1_ROOT]         = &pcie1_root_clk,
    [IMX8MQ_CLK_PCIE2_ROOT]         = &pcie2_root_clk,
    [IMX8MQ_CLK_PWM1_ROOT]          = &pwm1_root_clk,
    [IMX8MQ_CLK_PWM2_ROOT]          = &pwm2_root_clk,
    [IMX8MQ_CLK_PWM3_ROOT]          = &pwm3_root_clk,
    [IMX8MQ_CLK_PWM4_ROOT]          = &pwm4_root_clk,
    [IMX8MQ_CLK_QSPI_ROOT]          = &qspi_root_clk,
    [IMX8MQ_CLK_RAWNAND_ROOT]       = &nand_root_clk,
    [IMX8MQ_CLK_NAND_USDHC_BUS_RAWNAND_CLK] = &nand_usdhc_rawnand_clk,
    [IMX8MQ_CLK_SAI1_ROOT]          = &sai1_root_clk,
    [IMX8MQ_CLK_SAI1_IPG]           = &sai1_ipg_clk,
    [IMX8MQ_CLK_SAI2_ROOT]          = &sai2_root_clk,
    [IMX8MQ_CLK_SAI2_IPG]           = &sai2_ipg_clk,
    [IMX8MQ_CLK_SAI3_ROOT]          = &sai3_root_clk,
    [IMX8MQ_CLK_SAI3_IPG]           = &sai3_ipg_clk,
    [IMX8MQ_CLK_SAI4_ROOT]          = &sai4_root_clk,
    [IMX8MQ_CLK_SAI4_IPG]           = &sai4_ipg_clk,
    [IMX8MQ_CLK_SAI5_ROOT]          = &sai5_root_clk,
    [IMX8MQ_CLK_SAI5_IPG]           = &sai5_ipg_clk,
    [IMX8MQ_CLK_SAI6_ROOT]          = &sai6_root_clk,
    [IMX8MQ_CLK_SAI6_IPG]           = &sai6_ipg_clk,
    [IMX8MQ_CLK_UART1_ROOT]         = &uart1_root_clk,
    [IMX8MQ_CLK_UART2_ROOT]         = &uart2_root_clk,
    [IMX8MQ_CLK_UART3_ROOT]         = &uart3_root_clk,
    [IMX8MQ_CLK_UART4_ROOT]         = &uart4_root_clk,
    [IMX8MQ_CLK_USB1_CTRL_ROOT]     = &usb1_ctrl_root_clk,
    [IMX8MQ_CLK_USB2_CTRL_ROOT]     = &usb2_ctrl_root_clk,
    [IMX8MQ_CLK_USB1_PHY_ROOT]      = &usb1_phy_root_clk,
    [IMX8MQ_CLK_USB2_PHY_ROOT]      = &usb2_phy_root_clk,
    [IMX8MQ_CLK_USDHC1_ROOT]        = &usdhc1_root_clk,
    [IMX8MQ_CLK_USDHC2_ROOT]        = &usdhc2_root_clk,
    [IMX8MQ_CLK_WDOG1_ROOT]         = &wdog1_root_clk,
    [IMX8MQ_CLK_WDOG2_ROOT]         = &wdog2_root_clk,
    [IMX8MQ_CLK_WDOG3_ROOT]         = &wdog3_root_clk,
    [IMX8MQ_CLK_VPU_G1_ROOT]        = &vpu_g1_root_clk,
    [IMX8MQ_CLK_GPU_ROOT]           = &gpu_root_clk,
    [IMX8MQ_CLK_VPU_G2_ROOT]        = &vpu_g2_root_clk,
    [IMX8MQ_CLK_DISP_ROOT]          = &disp_root_clk,
    [IMX8MQ_CLK_DISP_AXI_ROOT]      = &disp_axi_root_clk,
    [IMX8MQ_CLK_DISP_APB_ROOT]      = &disp_apb_root_clk,
    [IMX8MQ_CLK_DISP_RTRM_ROOT]     = &disp_rtrm_root_clk,
    [IMX8MQ_CLK_TMU_ROOT]           = &tmu_root_clk,
    [IMX8MQ_CLK_VPU_DEC_ROOT]       = &vpu_dec_root_clk,
    [IMX8MQ_CLK_CSI1_ROOT]          = &csi1_root_clk,
    [IMX8MQ_CLK_CSI2_ROOT]          = &csi2_root_clk,
    [IMX8MQ_CLK_SDMA1_ROOT]         = &sdma1_clk,
    [IMX8MQ_CLK_SDMA2_ROOT]         = &sdma2_clk,
};

struct clk **get_clk_list(void)
{
    sddf_dprintf("get clk list\n");

    (void)arm_pll_ref_div;
    return imx8mq_clks;
}
