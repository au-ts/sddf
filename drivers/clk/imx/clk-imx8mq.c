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

/* static struct clk_parent_data imx8mq_dsi_ahb_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dram_alt_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys1_pll_100m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "sys1_pll_266m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dram_apb_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_vpu_g1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys1_pll_100m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_vpu_g2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys1_pll_100m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_disp_dtrc_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_disp_dc8000_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pcie1_ctrl_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys2_pll_333m", }, */
/*     { .name = "sys3_pll_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pcie1_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pcie1_aux_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_200m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dc_pixel_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_lcdif_pixel_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_sai1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "clk_ext2", }, */
/* }; */

/* static struct clk_parent_data imx8mq_sai2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/* }; */

/* static struct clk_parent_data imx8mq_sai3_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_sai4_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "clk_ext2", }, */
/* }; */

/* static struct clk_parent_data imx8mq_sai5_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/* }; */

/* static struct clk_parent_data imx8mq_sai6_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_spdif1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/* }; */

/* static struct clk_parent_data imx8mq_spdif2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_enet_ref_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "clk_ext4", }, */
/* }; */

/* static struct clk_parent_data imx8mq_enet_timer_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "clk_ext4", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_enet_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_nand_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_qspi_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys1_pll_100m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_usdhc1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_100m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_usdhc2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_100m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_i2c1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_i2c2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_i2c3_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_i2c4_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys1_pll_133m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_uart1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext4", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_uart2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_uart3_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext4", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_uart4_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_usb_core_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_100m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_usb_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_100m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_gic_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_ecspi1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_ecspi2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pwm1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pwm2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pwm3_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pwm4_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_gpt1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "clk_ext1", }, */
/* }; */

/* static struct clk_parent_data imx8mq_wdog_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_133m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys2_pll_166m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_wrclk_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys1_pll_100m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dsi_core_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dsi_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dsi_dbi_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_dsi_esc_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_csi1_core_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_csi1_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_csi1_esc_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_csi2_core_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_csi2_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_125m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "video_pll1_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_csi2_esc_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_1000m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pcie2_ctrl_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_266m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "sys2_pll_333m", }, */
/*     { .name = "sys3_pll_out", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pcie2_phy_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "clk_ext1", }, */
/*     { .name = "clk_ext2", }, */
/*     { .name = "clk_ext3", }, */
/*     { .name = "clk_ext4", }, */
/*     { .name = "sys1_pll_400m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_pcie2_aux_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys2_pll_50m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_100m", }, */
/*     { .name = "sys1_pll_80m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_200m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_ecspi3_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_40m", }, */
/*     { .name = "sys1_pll_160m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "sys2_pll_250m", }, */
/*     { .name = "audio_pll2_out", }, */
/* }; */

static struct clk_parent_data imx8mq_dram_core_sels[] = {
    { .name = "dram_pll_out", },
    { .name = "dram_alt_root", },
};

/* static struct clk_parent_data imx8mq_clko1_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys1_pll_800m", }, */
/*     { .name = "osc_27m", }, */
/*     { .name = "sys1_pll_200m", }, */
/*     { .name = "audio_pll2_out", }, */
/*     { .name = "sys2_pll_500m", }, */
/*     { .name = "vpu_pll_out", }, */
/*     { .name = "sys1_pll_80m", }, */
/* }; */

/* static struct clk_parent_data imx8mq_clko2_sels[] = { */
/*     { .name = "osc_25m", }, */
/*     { .name = "sys2_pll_200m", }, */
/*     { .name = "sys1_pll_400m", }, */
/*     { .name = "sys2_pll_166m", }, */
/*     { .name = "sys3_pll_out", }, */
/*     { .name = "audio_pll1_out", }, */
/*     { .name = "video_pll1_out", }, */
/*     { .name = "ckil", }, */
/* }; */

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
/* imx8m_clk_hw_fw_managed_composite("dram_alt", imx8mq_dram_alt_sels, base + 0xa000); */
/* imx8m_clk_hw_fw_managed_composite_critical("dram_apb", imx8mq_dram_apb_sels, base + 0xa080); */

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
};

struct clk **get_clk_list(void)
{
    sddf_dprintf("get clk list\n");

    (void)arm_pll_ref_div;
    return imx8mq_clks;
}
