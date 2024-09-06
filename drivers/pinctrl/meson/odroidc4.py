# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

# Document referenced: Linux: drivers/pinctrl/meson/pinctrl-meson-g12a.c

# This file defines how each pad of the chip map to each port.
# And how such mapping is defined in the DTS.

# Each GPIO chip has a list of pads, each assigned an index.

# First GPIO chip, AKA, the "Always-On" AO chip.
GPIOAO_0  = 0
GPIOAO_1  = 1
GPIOAO_2  = 2
GPIOAO_3  = 3
GPIOAO_4  = 4
GPIOAO_5  = 5
GPIOAO_6  = 6
GPIOAO_7  = 7
GPIOAO_8  = 8
GPIOAO_9  = 9
GPIOAO_10 = 10
GPIOAO_11 = 11
GPIOE_0   = 12
GPIOE_1   = 13
GPIOE_2   = 14

# Second and main GPIO chip, AKA peripherals
GPIOZ_0  = 0
GPIOZ_1  = 1
GPIOZ_2  = 2
GPIOZ_3  = 3
GPIOZ_4  = 4
GPIOZ_5  = 5
GPIOZ_6  = 6
GPIOZ_7  = 7
GPIOZ_8  = 8
GPIOZ_9  = 9
GPIOZ_10 = 10
GPIOZ_11 = 11
GPIOZ_12 = 12
GPIOZ_13 = 13
GPIOZ_14 = 14
GPIOZ_15 = 15
GPIOH_0  = 16
GPIOH_1  = 17
GPIOH_2  = 18
GPIOH_3  = 19
GPIOH_4  = 20
GPIOH_5  = 21
GPIOH_6  = 22
GPIOH_7  = 23
GPIOH_8  = 24
BOOT_0   = 25
BOOT_1   = 26
BOOT_2   = 27
BOOT_3   = 28
BOOT_4   = 29
BOOT_5   = 30
BOOT_6   = 31
BOOT_7   = 32
BOOT_8   = 33
BOOT_9   = 34
BOOT_10  = 35
BOOT_11  = 36
BOOT_12  = 37
BOOT_13  = 38
BOOT_14  = 39
BOOT_15  = 40
GPIOC_0  = 41
GPIOC_1  = 42
GPIOC_2  = 43
GPIOC_3  = 44
GPIOC_4  = 45
GPIOC_5  = 46
GPIOC_6  = 47
GPIOC_7  = 48
GPIOA_0  = 49
GPIOA_1  = 50
GPIOA_2  = 51
GPIOA_3  = 52
GPIOA_4  = 53
GPIOA_5  = 54
GPIOA_6  = 55
GPIOA_7  = 56
GPIOA_8  = 57
GPIOA_9  = 58
GPIOA_10 = 59
GPIOA_11 = 60
GPIOA_12 = 61
GPIOA_13 = 62
GPIOA_14 = 63
GPIOA_15 = 64
GPIOX_0  = 65
GPIOX_1  = 66
GPIOX_2  = 67
GPIOX_3  = 68
GPIOX_4  = 69
GPIOX_5  = 70
GPIOX_6  = 71
GPIOX_7  = 72
GPIOX_8  = 73
GPIOX_9  = 74
GPIOX_10 = 75
GPIOX_11 = 76
GPIOX_12 = 77
GPIOX_13 = 78
GPIOX_14 = 79
GPIOX_15 = 80
GPIOX_16 = 81
GPIOX_17 = 82
GPIOX_18 = 83
GPIOX_19 = 84

########################################################
AO_BASE             = 0xFF80_0000
AO_FIRST_REG_OFFSET = 0x0A

PERIPHS_BASE             = 0xFF63_4400
PERIPHS_FIRST_REG_OFFSET = 0xB0

########################################################
# Then each port is assigned a pad. Hardcoded in the driver.

port_to_pad = {
    # emmc:
    "emmc_nand_d0" : BOOT_0,
    "emmc_nand_d1" : BOOT_1,
    "emmc_nand_d2" : BOOT_2,
    "emmc_nand_d3" : BOOT_3,
    "emmc_nand_d4" : BOOT_4,
    "emmc_nand_d5" : BOOT_5,
    "emmc_nand_d6" : BOOT_6,
    "emmc_nand_d7" : BOOT_7,
    "emmc_clk"     : BOOT_8,
    "emmc_cmd"     : BOOT_10,
    "emmc_nand_ds" : BOOT_13,

    # nand:
    "nand_wen_clk" : BOOT_8,
    "nand_ale"     : BOOT_9,
    "nand_cle"     : BOOT_10,
    "nand_ce0"     : BOOT_11,
    "nand_ren_wr"  : BOOT_12,
    "nand_rb0"     : BOOT_14,
    "nand_ce1"     : BOOT_15,

    # nor
    "nor_hold" : BOOT_3,
    "nor_d"    : BOOT_4,
    "nor_q"    : BOOT_5,
    "nor_c"    : BOOT_6,
    "nor_wp"   : BOOT_7,
    "nor_cs"   : BOOT_14,

    # sdio
    "sdio_d0"  : GPIOX_0,
    "sdio_d1"  : GPIOX_1,
    "sdio_d2"  : GPIOX_2,
    "sdio_d3"  : GPIOX_3,
    "sdio_clk" : GPIOX_4,
    "sdio_cmd" : GPIOX_5,

    # sdcard
    "sdcard_d0_c"  : GPIOC_0,
    "sdcard_d1_c"  : GPIOC_1,
    "sdcard_d2_c"  : GPIOC_2,
    "sdcard_d3_c"  : GPIOC_3,
    "sdcard_clk_c" : GPIOC_4,
    "sdcard_cmd_c" : GPIOC_5,

    "sdcard_d0_z"  : GPIOZ_2,
    "sdcard_d1_z"  : GPIOZ_3,
    "sdcard_d2_z"  : GPIOZ_4,
    "sdcard_d3_z"  : GPIOZ_5,
    "sdcard_clk_z" : GPIOZ_6,
    "sdcard_cmd_z" : GPIOZ_7,

    # spi0
    "spi0_mosi_c" : GPIOC_0,
    "spi0_miso_c" : GPIOC_1,
    "spi0_ss0_c"  : GPIOC_2,
    "spi0_clk_c"  : GPIOC_3,

    "spi0_mosi_x" : GPIOX_8,
    "spi0_miso_x" : GPIOX_9,
    "spi0_ss0_x"  : GPIOX_10,
    "spi0_clk_x"  : GPIOX_11,

    # spi1
    "spi1_mosi" : GPIOH_4,
    "spi1_miso" : GPIOH_5,
    "spi1_ss0"  : GPIOH_6,
    "spi1_clk"  : GPIOH_7,

    # i2c0
    "i2c0_sda_c"  : GPIOC_5,
    "i2c0_sck_c"  : GPIOC_6,
    "i2c0_sda_z0" : GPIOZ_0,
    "i2c0_sck_z1" : GPIOZ_1,
    "i2c0_sda_z7" : GPIOZ_7,
    "i2c0_sck_z8" : GPIOZ_8,

    # i2c1
    "i2c1_sda_x"  : GPIOX_10,
    "i2c1_sck_x"  : GPIOX_11,
    "i2c1_sda_h2" : GPIOH_2,
    "i2c1_sck_h3" : GPIOH_3,
    "i2c1_sda_h6" : GPIOH_6,
    "i2c1_sck_h7" : GPIOH_7,

    # i2c2
    "i2c2_sda_x" : GPIOX_17,
    "i2c2_sck_x" : GPIOX_18,
    "i2c2_sda_z" : GPIOZ_14,
    "i2c2_sck_z" : GPIOZ_15,

    # i2c3
    "i2c3_sda_h" : GPIOH_0,
    "i2c3_sck_h" : GPIOH_1,
    "i2c3_sda_a" : GPIOA_14,
    "i2c3_sck_a" : GPIOA_15,

    # uart_a
    "uart_a_tx"  : GPIOX_12,
    "uart_a_rx"  : GPIOX_13,
    "uart_a_cts" : GPIOX_14,
    "uart_a_rts" : GPIOX_15,

    # uart_b
    "uart_b_tx" : GPIOX_6,
    "uart_b_rx" : GPIOX_7,

    # uart_c
    "uart_c_rts" : GPIOH_4,
    "uart_c_cts" : GPIOH_5,
    "uart_c_rx"  : GPIOH_6,
    "uart_c_tx"  : GPIOH_7,

    # uart_ao_a_c
    "uart_ao_a_rx_c" : GPIOC_2,
    "uart_ao_a_tx_c" : GPIOC_3,

    # iso7816
    "iso7816_clk_c"  : GPIOC_5,
    "iso7816_data_c" : GPIOC_6,
    "iso7816_clk_x"  : GPIOX_8,
    "iso7816_data_x" : GPIOX_9,
    "iso7816_clk_h"  : GPIOH_6,
    "iso7816_data_h" : GPIOH_7,
    "iso7816_clk_z"  : GPIOZ_0,
    "iso7816_data_z" : GPIOZ_1,

    # eth
    "eth_mdio"         : GPIOZ_0,
    "eth_mdc"          : GPIOZ_1,
    "eth_rgmii_rx_clk" : GPIOZ_2,
    "eth_rx_dv"        : GPIOZ_3,
    "eth_rxd0"         : GPIOZ_4,
    "eth_rxd1"         : GPIOZ_5,
    "eth_rxd2_rgmii"   : GPIOZ_6,
    "eth_rxd3_rgmii"   : GPIOZ_7,
    "eth_rgmii_tx_clk" : GPIOZ_8,
    "eth_txen"         : GPIOZ_9,
    "eth_txd0"         : GPIOZ_10,
    "eth_txd1"         : GPIOZ_11,
    "eth_txd2_rgmii"   : GPIOZ_12,
    "eth_txd3_rgmii"   : GPIOZ_13,
    "eth_link_led"     : GPIOZ_14,
    "eth_act_led"      : GPIOZ_15,

    # pwm_a
    "pwm_a" : GPIOX_6,

    # pwm_b
    "pwm_b_x7"  : GPIOX_7,
    "pwm_b_x19" : GPIOX_19,

    # pwm_c
    "pwm_c_c"  : GPIOC_4,
    "pwm_c_x5" : GPIOX_5,
    "pwm_c_x8" : GPIOX_8,

    # pwm_d
    "pwm_d_x3" : GPIOX_3,
    "pwm_d_x6" : GPIOX_6,

    # pwm_e
    "pwm_e" : GPIOX_16,

    # pwm_f
    "pwm_f_z" : GPIOZ_12,
    "pwm_f_a" : GPIOA_11,
    "pwm_f_x" : GPIOX_7,
    "pwm_f_h" : GPIOH_5,

    # cec_ao 
    "cec_ao_a_h" : GPIOH_3,
    "cec_ao_b_h" : GPIOH_3,

    # jtag_b
    "jtag_b_tdo" : GPIOC_0,
    "jtag_b_tdi" : GPIOC_1,
    "jtag_b_clk" : GPIOC_4,
    "jtag_b_tms" : GPIOC_5,

    # bt565_a
    "bt565_a_vs"   : GPIOZ_0,
    "bt565_a_hs"   : GPIOZ_1,
    "bt565_a_clk"  : GPIOZ_3,
    "bt565_a_din0" : GPIOZ_4,
    "bt565_a_din1" : GPIOZ_5,
    "bt565_a_din2" : GPIOZ_6,
    "bt565_a_din3" : GPIOZ_7,
    "bt565_a_din4" : GPIOZ_8,
    "bt565_a_din5" : GPIOZ_9,
    "bt565_a_din6" : GPIOZ_10,
    "bt565_a_din7" : GPIOZ_11,

    # tsin_a 
    "tsin_a_valid" : GPIOX_2,
    "tsin_a_sop"   : GPIOX_1,
    "tsin_a_din0"  : GPIOX_0,
    "tsin_a_clk"   : GPIOX_3,

    # tsin_b
    "tsin_b_valid_x" : GPIOX_9,
    "tsin_b_sop_x"   : GPIOX_8,
    "tsin_b_din0_x"  : GPIOX_10,
    "tsin_b_clk_x"   : GPIOX_11,

    "tsin_b_valid_z" : GPIOZ_2,
    "tsin_b_sop_z"   : GPIOZ_3,
    "tsin_b_din0_z"  : GPIOZ_4,
    "tsin_b_clk_z"   : GPIOZ_5,

    "tsin_b_fail" : GPIOZ_6,
    "tsin_b_din1" : GPIOZ_7,
    "tsin_b_din2" : GPIOZ_8,
    "tsin_b_din3" : GPIOZ_9,
    "tsin_b_din4" : GPIOZ_10,
    "tsin_b_din5" : GPIOZ_11,
    "tsin_b_din6" : GPIOZ_12,
    "tsin_b_din7" : GPIOZ_13,

    # hdmitx
    "hdmitx_sda"    : GPIOH_0,
    "hdmitx_sck"    : GPIOH_1,
    "hdmitx_hpd_in" : GPIOH_2,

    # pdm
    "pdm_din0_c" : GPIOC_0,
    "pdm_din1_c" : GPIOC_1,
    "pdm_din2_c" : GPIOC_2,
    "pdm_din3_c" : GPIOC_3,
    "pdm_dclk_c" : GPIOC_4,

    "pdm_din0_x" : GPIOX_0,
    "pdm_din1_x" : GPIOX_1,
    "pdm_din2_x" : GPIOX_2,
    "pdm_din3_x" : GPIOX_3,
    "pdm_dclk_x" : GPIOX_4,

    "pdm_din0_z" : GPIOZ_2,
    "pdm_din1_z" : GPIOZ_3,
    "pdm_din2_z" : GPIOZ_4,
    "pdm_din3_z" : GPIOZ_5,
    "pdm_dclk_z" : GPIOZ_6,

    "pdm_din0_a" : GPIOA_8,
    "pdm_din1_a" : GPIOA_9,
    "pdm_din2_a" : GPIOA_6,
    "pdm_din3_a" : GPIOA_5,
    "pdm_dclk_a" : GPIOA_7,

    # spdif_in
    "spdif_in_h"   : GPIOH_5,
    "spdif_in_a10" : GPIOA_10,
    "spdif_in_a12" : GPIOA_12,

    # spdif_out
    "spdif_out_h"   : GPIOH_4,
    "spdif_out_a11" : GPIOA_11,
    "spdif_out_a13" : GPIOA_13,

    # mclk0
    "mclk0_a" : GPIOA_0,

    # mclk1
    "mclk1_x" : GPIOX_5,
    "mclk1_z" : GPIOZ_8,
    "mclk1_a" : GPIOA_11,

    # tdm
    "tdm_a_slv_sclk" : GPIOX_11,
    "tdm_a_slv_fs"   : GPIOX_10,
    "tdm_a_sclk"     : GPIOX_11,
    "tdm_a_fs"       : GPIOX_10,
    "tdm_a_din0"     : GPIOX_9,
    "tdm_a_din1"     : GPIOX_8,
    "tdm_a_dout0"    : GPIOX_9,
    "tdm_a_dout1"    : GPIOX_8,

    "tdm_b_slv_sclk" : GPIOA_1,
    "tdm_b_slv_fs"   : GPIOA_2,
    "tdm_b_sclk"     : GPIOA_1,
    "tdm_b_fs"       : GPIOA_2,
    "tdm_b_din0"     : GPIOA_3,
    "tdm_b_din1"     : GPIOA_4,
    "tdm_b_din2"     : GPIOA_5,
    "tdm_b_din3_a"   : GPIOA_6,
    "tdm_b_din3_h"   : GPIOH_5,
    "tdm_b_dout0"    : GPIOA_3,
    "tdm_b_dout1"    : GPIOA_4,
    "tdm_b_dout2"    : GPIOA_5,
    "tdm_b_dout3_a"  : GPIOA_6,
    "tdm_b_dout3_h"  : GPIOH_5,

    "tdm_c_slv_sclk_a" : GPIOA_12,
    "tdm_c_slv_fs_a"   : GPIOA_13,
    "tdm_c_slv_sclk_z" : GPIOZ_7,
    "tdm_c_slv_fs_z"   : GPIOZ_6,
    "tdm_c_sclk_a"     : GPIOA_12,
    "tdm_c_fs_a"       : GPIOA_13,
    "tdm_c_sclk_z"     : GPIOZ_7,
    "tdm_c_fs_z"       : GPIOZ_6,
    "tdm_c_din0_a"     : GPIOA_10,
    "tdm_c_din1_a"     : GPIOA_9,
    "tdm_c_din2_a"     : GPIOA_8,
    "tdm_c_din3_a"     : GPIOA_7,
    "tdm_c_din0_z"     : GPIOZ_2,
    "tdm_c_din1_z"     : GPIOZ_3,
    "tdm_c_din2_z"     : GPIOZ_4,
    "tdm_c_din3_z"     : GPIOZ_5,
    "tdm_c_dout0_a"    : GPIOA_10,
    "tdm_c_dout1_a"    : GPIOA_9,
    "tdm_c_dout2_a"    : GPIOA_8,
    "tdm_c_dout3_a"    : GPIOA_7,
    "tdm_c_dout0_z"    : GPIOZ_2,
    "tdm_c_dout1_z"    : GPIOZ_3,
    "tdm_c_dout2_z"    : GPIOZ_4,
    "tdm_c_dout3_z"    : GPIOZ_5,
}

ao_port_to_pad = {
    # uart_ao_a
    "uart_ao_a_tx_pins"  : GPIOAO_0,
    "uart_ao_a_rx_pins"  : GPIOAO_1,
    "uart_ao_a_cts_pins" : GPIOE_0,
    "uart_ao_a_rts_pins" : GPIOE_1,

    # uart_ao_b
    "uart_ao_b_tx_2_pins" : GPIOAO_2,
    "uart_ao_b_rx_3_pins" : GPIOAO_3,
    "uart_ao_b_tx_8_pins" : GPIOAO_8,
    "uart_ao_b_rx_9_pins" : GPIOAO_9,
    "uart_ao_b_cts_pins"  : GPIOE_0,
    "uart_ao_b_rts_pins"  : GPIOE_1,

    # i2c_ao
    "i2c_ao_sck_pins" : GPIOAO_2,
    "i2c_ao_sda_pins" : GPIOAO_3,

    "i2c_ao_sck_e_pins" : GPIOE_0,
    "i2c_ao_sda_e_pins" : GPIOE_1,

    # i2c_ao_slave
    "i2c_ao_slave_sck_pins" : GPIOAO_2,
    "i2c_ao_slave_sda_pins" : GPIOAO_3,

    # ir_in
    "remote_ao_input_pins" : GPIOAO_5,

    # ir_out
    "remote_ao_out_pins" : GPIOAO_4,

    # pwm_a_e
    "pwm_a_e_pins" : GPIOE_2,

    # pwm_ao_a
    "pwm_ao_a_pins" : GPIOAO_11,
    "pwm_ao_a_hiz_pins" : GPIOAO_11,

    # pwm_ao_b
    "pwm_ao_b_pins" : GPIOE_0,

    # pwm_ao_c
    "pwm_ao_c_4_pins" : GPIOAO_4,
    "pwm_ao_c_hiz_pins" : GPIOAO_4,
    "pwm_ao_c_6_pins" : GPIOAO_6,

    # pwm_ao_d
    "pwm_ao_d_5_pins" : GPIOAO_5,
    "pwm_ao_d_10_pins" : GPIOAO_10,
    "pwm_ao_d_e_pins" : GPIOE_1,

    # jtag_a
    "jtag_a_tdi_pins" : GPIOAO_8,
    "jtag_a_tdo_pins" : GPIOAO_9,
    "jtag_a_clk_pins" : GPIOAO_6,
    "jtag_a_tms_pins" : GPIOAO_7,

    # cec_ao
    "cec_ao_a_pins" : GPIOAO_10,
    "cec_ao_b_pins" : GPIOAO_10,

    # tsin_ao_a
    "tsin_ao_asop_pins" : GPIOAO_6,
    "tsin_ao_adin0_pins" : GPIOAO_7,
    "tsin_ao_aclk_pins" : GPIOAO_8,
    "tsin_ao_a_valid_pins" : GPIOAO_9,

    # spdif_ao_out
    "spdif_ao_out_pins" : GPIOAO_10,

    # tdm_ao_b
    "tdm_ao_b_slv_fs_pins" : GPIOAO_7,
    "tdm_ao_b_slv_sclk_pins" : GPIOAO_8,
    "tdm_ao_b_fs_pins" : GPIOAO_7,
    "tdm_ao_b_sclk_pins" : GPIOAO_8,
    "tdm_ao_b_din0_pins" : GPIOAO_4,
    "tdm_ao_b_din1_pins" : GPIOAO_10,
    "tdm_ao_b_din2_pins" : GPIOAO_6,
    "tdm_ao_b_dout0_pins" : GPIOAO_4,
    "tdm_ao_b_dout1_pins" : GPIOAO_10,
    "tdm_ao_b_dout2_pins" : GPIOAO_6,

    # mclk0_ao
    "mclk0_ao_pins" : GPIOAO_9,
}

########################################################
# To represent the above in hardware, each pad has a 3 bits integer mux value.
# To indicate what port it is muxed to.
# All pads are assigned function 0 by default, then these values override it.

port_to_mux_func = {
    # bank BOOT
    "emmc_nand_d0" : 1,
    "emmc_nand_d1" : 1,
    "emmc_nand_d2" : 1,
    "emmc_nand_d3" : 1,
    "emmc_nand_d4" : 1,
    "emmc_nand_d5" : 1,
    "emmc_nand_d6" : 1,
    "emmc_nand_d7" : 1,
    "emmc_clk"     : 1,
    "emmc_cmd"     : 1,
    "emmc_nand_ds" : 1,
    "nand_ce0"     : 2,
    "nand_ale"     : 2,
    "nand_cle"     : 2,
    "nand_wen_clk" : 2,
    "nand_ren_wr"  : 2,
    "nand_rb0"     : 2,
    "nand_ce1"     : 2,
    "nor_hold"     : 3,
    "nor_d"        : 3,
    "nor_q"        : 3,
    "nor_c"        : 3,
    "nor_wp"       : 3,
    "nor_cs"       : 3,

    # bank GPIOZ
    "sdcard_d0_z"      : 5,
    "sdcard_d1_z"      : 5,
    "sdcard_d2_z"      : 5,
    "sdcard_d3_z"      : 5,
    "sdcard_clk_z"     : 5,
    "sdcard_cmd_z"     : 5,
    "i2c0_sda_z0"      : 4,
    "i2c0_sck_z1"      : 4,
    "i2c0_sda_z7"      : 7,
    "i2c0_sck_z8"      : 7,
    "i2c2_sda_z"       : 3,
    "i2c2_sck_z"       : 3,
    "iso7816_clk_z"    : 3,
    "iso7816_data_z"   : 3,
    "eth_mdio"         : 1,
    "eth_mdc"          : 1,
    "eth_rgmii_rx_clk" : 1,
    "eth_rx_dv"        : 1,
    "eth_rxd0"         : 1,
    "eth_rxd1"         : 1,
    "eth_rxd2_rgmii"   : 1,
    "eth_rxd3_rgmii"   : 1,
    "eth_rgmii_tx_clk" : 1,
    "eth_txen"         : 1,
    "eth_txd0"         : 1,
    "eth_txd1"         : 1,
    "eth_txd2_rgmii"   : 1,
    "eth_txd3_rgmii"   : 1,
    "eth_link_led"     : 1,
    "eth_act_led"      : 1,
    "bt565_a_vs"       : 2,
    "bt565_a_hs"       : 2,
    "bt565_a_clk"      : 2,
    "bt565_a_din0"     : 2,
    "bt565_a_din1"     : 2,
    "bt565_a_din2"     : 2,
    "bt565_a_din3"     : 2,
    "bt565_a_din4"     : 2,
    "bt565_a_din5"     : 2,
    "bt565_a_din6"     : 2,
    "bt565_a_din7"     : 2,
    "tsin_b_valid_z"   : 3,
    "tsin_b_sop_z"     : 3,
    "tsin_b_din0_z"    : 3,
    "tsin_b_clk_z"     : 3,
    "tsin_b_fail"      : 3,
    "tsin_b_din1"      : 3,
    "tsin_b_din2"      : 3,
    "tsin_b_din3"      : 3,
    "tsin_b_din4"      : 3,
    "tsin_b_din5"      : 3,
    "tsin_b_din6"      : 3,
    "tsin_b_din7"      : 3,
    "pdm_din0_z"       : 7,
    "pdm_din1_z"       : 7,
    "pdm_din2_z"       : 7,
    "pdm_din3_z"       : 7,
    "pdm_dclk_z"       : 7,
    "tdm_c_slv_sclk_z" : 6,
    "tdm_c_slv_fs_z"   : 6,
    "tdm_c_din0_z"     : 6,
    "tdm_c_din1_z"     : 6,
    "tdm_c_din2_z"     : 6,
    "tdm_c_din3_z"     : 6,
    "tdm_c_sclk_z"     : 4,
    "tdm_c_fs_z"       : 4,
    "tdm_c_dout0_z"    : 4,
    "tdm_c_dout1_z"    : 4,
    "tdm_c_dout2_z"    : 4,
    "tdm_c_dout3_z"    : 4,
    "mclk1_z"          : 4,
    "pwm_f_z"          : 5,

    # bank GPIOX
    "sdio_d0"         : 1,
    "sdio_d1"         : 1,
    "sdio_d2"         : 1,
    "sdio_d3"         : 1,
    "sdio_clk"        : 1,
    "sdio_cmd"        : 1,
    "spi0_mosi_x"     : 4,
    "spi0_miso_x"     : 4,
    "spi0_ss0_x"      : 4,
    "spi0_clk_x"      : 4,
    "i2c1_sda_x"      : 5,
    "i2c1_sck_x"      : 5,
    "i2c2_sda_x"      : 1,
    "i2c2_sck_x"      : 1,
    "uart_a_tx"       : 1,
    "uart_a_rx"       : 1,
    "uart_a_cts"      : 1,
    "uart_a_rts"      : 1,
    "uart_b_tx"       : 2,
    "uart_b_rx"       : 2,
    "iso7816_clk_x"   : 6,
    "iso7816_data_x"  : 6,
    "pwm_a"           : 1,
    "pwm_b_x7"        : 4,
    "pwm_b_x19"       : 1,
    "pwm_c_x5"        : 4,
    "pwm_c_x8"        : 5,
    "pwm_d_x3"        : 4,
    "pwm_d_x6"        : 4,
    "pwm_e"           : 1,
    "pwm_f_x"         : 1,
    "tsin_a_valid"    : 3,
    "tsin_a_sop"      : 3,
    "tsin_a_din0"     : 3,
    "tsin_a_clk"      : 3,
    "tsin_b_valid_x"  : 3,
    "tsin_b_sop_x"    : 3,
    "tsin_b_din0_x"   : 3,
    "tsin_b_clk_x"    : 3,
    "pdm_din0_x"      : 2,
    "pdm_din1_x"      : 2,
    "pdm_din2_x"      : 2,
    "pdm_din3_x"      : 2,
    "pdm_dclk_x"      : 2,
    "tdm_a_slv_sclk"  : 2,
    "tdm_a_slv_fs"    : 2,
    "tdm_a_din0"      : 2,
    "tdm_a_din1"      : 2,
    "tdm_a_sclk"      : 1,
    "tdm_a_fs"        : 1,
    "tdm_a_dout0"     : 1,
    "tdm_a_dout1"     : 1,
    "mclk1_x"         : 2,

    # bank GPIOC
    "sdcard_d0_c"    : 1,
    "sdcard_d1_c"    : 1,
    "sdcard_d2_c"    : 1,
    "sdcard_d3_c"    : 1,
    "sdcard_clk_c"   : 1,
    "sdcard_cmd_c"   : 1,
    "spi0_mosi_c"    : 5,
    "spi0_miso_c"    : 5,
    "spi0_ss0_c"     : 5,
    "spi0_clk_c"     : 5,
    "i2c0_sda_c"     : 3,
    "i2c0_sck_c"     : 3,
    "uart_ao_a_rx_c" : 2,
    "uart_ao_a_tx_c" : 2,
    "iso7816_clk_c"  : 5,
    "iso7816_data_c" : 5,
    "pwm_c_c"        : 5,
    "jtag_b_tdo"     : 2,
    "jtag_b_tdi"     : 2,
    "jtag_b_clk"     : 2,
    "jtag_b_tms"     : 2,
    "pdm_din0_c"     : 4,
    "pdm_din1_c"     : 4,
    "pdm_din2_c"     : 4,
    "pdm_din3_c"     : 4,
    "pdm_dclk_c"     : 4,

    # bank GPIOH
    "spi1_mosi"      : 3,
    "spi1_miso"      : 3,
    "spi1_ss0"       : 3,
    "spi1_clk"       : 3,
    "i2c1_sda_h2"    : 2,
    "i2c1_sck_h3"    : 2,
    "i2c1_sda_h6"    : 4,
    "i2c1_sck_h7"    : 4,
    "i2c3_sda_h"     : 2,
    "i2c3_sck_h"     : 2,
    "uart_c_tx"      : 2,
    "uart_c_rx"      : 2,
    "uart_c_cts"     : 2,
    "uart_c_rts"     : 2,
    "iso7816_clk_h"  : 1,
    "iso7816_data_h" : 1,
    "pwm_f_h"        : 4,
    "cec_ao_a_h"     : 4,
    "cec_ao_b_h"     : 5,
    "hdmitx_sda"     : 1,
    "hdmitx_sck"     : 1,
    "hdmitx_hpd_in"  : 1,
    "spdif_out_h"    : 1,
    "spdif_in_h"     : 1,
    "tdm_b_din3_h"   : 6,
    "tdm_b_dout3_h"  : 5,

    # bank GPIOA
    "i2c3_sda_a"       : 2,
    "i2c3_sck_a"       : 2,
    "pdm_din0_a"       : 1,
    "pdm_din1_a"       : 1,
    "pdm_din2_a"       : 1,
    "pdm_din3_a"       : 1,
    "pdm_dclk_a"       : 1,
    "spdif_in_a10"     : 1,
    "spdif_in_a12"     : 1,
    "spdif_out_a11"    : 1,
    "spdif_out_a13"    : 1,
    "tdm_b_slv_sclk"   : 2,
    "tdm_b_slv_fs"     : 2,
    "tdm_b_din0"       : 2,
    "tdm_b_din1"       : 2,
    "tdm_b_din2"       : 2,
    "tdm_b_din3_a"     : 2,
    "tdm_b_sclk"       : 1,
    "tdm_b_fs"         : 1,
    "tdm_b_dout0"      : 1,
    "tdm_b_dout1"      : 1,
    "tdm_b_dout2"      : 3,
    "tdm_b_dout3_a"    : 3,
    "tdm_c_slv_sclk_a" : 3,
    "tdm_c_slv_fs_a"   : 3,
    "tdm_c_din0_a"     : 3,
    "tdm_c_din1_a"     : 3,
    "tdm_c_din2_a"     : 3,
    "tdm_c_din3_a"     : 3,
    "tdm_c_sclk_a"     : 2,
    "tdm_c_fs_a"       : 2,
    "tdm_c_dout0_a"    : 2,
    "tdm_c_dout1_a"    : 2,
    "tdm_c_dout2_a"    : 2,
    "tdm_c_dout3_a"    : 2,
    "mclk0_a"          : 1,
    "mclk1_a"          : 2,
    "pwm_f_a"          : 3,
}

ao_port_to_mux_func = {
    "uart_ao_a_tx"      : 1,
    "uart_ao_a_rx"      : 1,
    "uart_ao_a_cts"     : 1,
    "uart_ao_a_rts"     : 1,
    "uart_ao_b_tx_2"    : 2,
    "uart_ao_b_rx_3"    : 2,
    "uart_ao_b_tx_8"    : 3,
    "uart_ao_b_rx_9"    : 3,
    "uart_ao_b_cts"     : 2,
    "uart_ao_b_rts"     : 2,
    "i2c_ao_sck"        : 1,
    "i2c_ao_sda"        : 1,
    "i2c_ao_sck_e"      : 4,
    "i2c_ao_sda_e"      : 4,
    "i2c_ao_slave_sck"  : 3,
    "i2c_ao_slave_sda"  : 3,
    "remote_ao_input"   : 1,
    "remote_ao_out"     : 1,
    "pwm_a_e"           : 3,
    "pwm_ao_a"          : 3,
    "pwm_ao_a_hiz"      : 2,
    "pwm_ao_b"          : 3,
    "pwm_ao_c_4"        : 3,
    "pwm_ao_c_hiz"      : 4,
    "pwm_ao_c_6"        : 3,
    "pwm_ao_d_5"        : 3,
    "pwm_ao_d_10"       : 3,
    "pwm_ao_d_e"        : 3,
    "jtag_a_tdi"        : 1,
    "jtag_a_tdo"        : 1,
    "jtag_a_clk"        : 1,
    "jtag_a_tms"        : 1,
    "cec_ao_a"          : 1,
    "cec_ao_b"          : 2,
    "tsin_ao_asop"      : 4,
    "tsin_ao_adin0"     : 4,
    "tsin_ao_aclk"      : 4,
    "tsin_ao_a_valid"   : 4,
    "spdif_ao_out"      : 4,
    "tdm_ao_b_dout0"    : 5,
    "tdm_ao_b_dout1"    : 5,
    "tdm_ao_b_dout2"    : 5,
    "tdm_ao_b_fs"       : 5,
    "tdm_ao_b_sclk"     : 5,
    "tdm_ao_b_din0"     : 6,
    "tdm_ao_b_din1"     : 6,
    "tdm_ao_b_din2"     : 6,
    "tdm_ao_b_slv_fs"   : 6,
    "tdm_ao_b_slv_sclk" : 6,
    "mclk0_ao"          : 5,
}

########################################################
# All ports are grouped into a common name.
# Then each port are assigned a function in the DTS, encoded as a string.

function_to_group = {
    "gpio_periphs": [ "GPIOZ_0", "GPIOZ_1", "GPIOZ_2", "GPIOZ_3", "GPIOZ_4",
                      "GPIOZ_5", "GPIOZ_6", "GPIOZ_7", "GPIOZ_8", "GPIOZ_9",
                      "GPIOZ_10", "GPIOZ_11", "GPIOZ_12", "GPIOZ_13", "GPIOZ_14",
                      "GPIOZ_15",

                      "GPIOH_0", "GPIOH_1", "GPIOH_2", "GPIOH_3", "GPIOH_4",
                      "GPIOH_5", "GPIOH_6", "GPIOH_7", "GPIOH_8",

                      "BOOT_0", "BOOT_1", "BOOT_2", "BOOT_3", "BOOT_4",
                      "BOOT_5", "BOOT_6", "BOOT_7", "BOOT_8", "BOOT_9",
                      "BOOT_10", "BOOT_11", "BOOT_12", "BOOT_13", "BOOT_14",
                      "BOOT_15",

                      "GPIOC_0", "GPIOC_1", "GPIOC_2", "GPIOC_3", "GPIOC_4",
                      "GPIOC_5", "GPIOC_6", "GPIOC_7",

                      "GPIOA_0", "GPIOA_1", "GPIOA_2", "GPIOA_3", "GPIOA_4",
                      "GPIOA_5", "GPIOA_6", "GPIOA_7", "GPIOA_8", "GPIOA_9",
                      "GPIOA_10", "GPIOA_11", "GPIOA_12", "GPIOA_13", "GPIOA_14",
                      "GPIOA_15",

                      "GPIOX_0", "GPIOX_1", "GPIOX_2", "GPIOX_3", "GPIOX_4",
                      "GPIOX_5", "GPIOX_6", "GPIOX_7", "GPIOX_8", "GPIOX_9",
                      "GPIOX_10", "GPIOX_11", "GPIOX_12", "GPIOX_13", "GPIOX_14",
                      "GPIOX_15", "GPIOX_16", "GPIOX_17", "GPIOX_18", "GPIOX_19" ],

    "emmc": [ "emmc_nand_d0", "emmc_nand_d1", "emmc_nand_d2",
              "emmc_nand_d3", "emmc_nand_d4", "emmc_nand_d5",
              "emmc_nand_d6", "emmc_nand_d7",
              "emmc_clk", "emmc_cmd", "emmc_nand_ds" ],

    "nand": [ "emmc_nand_d0", "emmc_nand_d1", "emmc_nand_d2",
              "emmc_nand_d3", "emmc_nand_d4", "emmc_nand_d5",
              "emmc_nand_d6", "emmc_nand_d7",
              "nand_ce0", "nand_ale", "nand_cle",
              "nand_wen_clk", "nand_ren_wr", "nand_rb0",
              "emmc_nand_ds", "nand_ce1" ],
    
    "nor": [ "nor_d", "nor_q", "nor_c", "nor_cs",
             "nor_hold", "nor_wp" ],
    
    "sdio": [ "sdio_d0", "sdio_d1", "sdio_d2", "sdio_d3",
              "sdio_cmd", "sdio_clk", "sdio_dummy" ],
    
    "sdcard": [ "sdcard_d0_c", "sdcard_d1_c", "sdcard_d2_c", "sdcard_d3_c",
                "sdcard_clk_c", "sdcard_cmd_c",
                "sdcard_d0_z", "sdcard_d1_z", "sdcard_d2_z", "sdcard_d3_z",
                "sdcard_clk_z", "sdcard_cmd_z" ],

    "spi0": [ "spi0_mosi_c", "spi0_miso_c", "spi0_ss0_c", "spi0_clk_c",
              "spi0_mosi_x", "spi0_miso_x", "spi0_ss0_x", "spi0_clk_x" ],
    
    "spi1": [ "spi1_mosi", "spi1_miso", "spi1_ss0", "spi1_clk" ],

    "i2c0": [ "i2c0_sda_c", "i2c0_sck_c",
              "i2c0_sda_z0", "i2c0_sck_z1",
              "i2c0_sda_z7", "i2c0_sck_z8" ],

    "i2c1": [ "i2c1_sda_x", "i2c1_sck_x",
              "i2c1_sda_h2", "i2c1_sck_h3",
              "i2c1_sda_h6", "i2c1_sck_h7" ],
    
    "i2c2": [ "i2c2_sda_x", "i2c2_sck_x",
              "i2c2_sda_z", "i2c2_sck_z" ],
    
    "i2c3": [ "i2c3_sda_h", "i2c3_sck_h",
              "i2c3_sda_a", "i2c3_sck_a" ],
    
    "uart_a": [ "uart_a_tx", "uart_a_rx", "uart_a_cts", "uart_a_rts" ],

    "uart_b": [ "uart_b_tx", "uart_b_rx" ],

    "uart_c": [ "uart_c_tx", "uart_c_rx", "uart_c_cts", "uart_c_rts" ],

    "uart_ao_a_c": [ "uart_ao_a_rx_c", "uart_ao_a_tx_c" ],

    "iso7816": [ "iso7816_clk_c", "iso7816_data_c",
                 "iso7816_clk_x", "iso7816_data_x",
                 "iso7816_clk_h", "iso7816_data_h",
                 "iso7816_clk_z", "iso7816_data_z" ],

    "eth": [ "eth_rxd2_rgmii", "eth_rxd3_rgmii", "eth_rgmii_tx_clk",
             "eth_txd2_rgmii", "eth_txd3_rgmii", "eth_rgmii_rx_clk",
             "eth_txd0", "eth_txd1", "eth_txen", "eth_mdc",
             "eth_rxd0", "eth_rxd1", "eth_rx_dv", "eth_mdio",
             "eth_link_led", "eth_act_led" ],
    
    "pwm_a": [ "pwm_a" ],

    "pwm_b": [ "pwm_b_x7", "pwm_b_x19" ],

    "pwm_c": [ "pwm_c_c", "pwm_c_x5", "pwm_c_x8" ],

    "pwm_d": [ "pwm_d_x3", "pwm_d_x6" ],

    "pwm_e": [ "pwm_f_z", "pwm_f_a", "pwm_f_x", "pwm_f_h" ],

    "cec_ao_a_h": [ "cec_ao_a_h" ],

    "cec_ao_b_h": [ "cec_ao_b_h" ],

    "jtag_b": [ "jtag_b_tdi", "jtag_b_tdo", "jtag_b_clk", "jtag_b_tms" ],

    "bt565_a": [ "bt565_a_vs", "bt565_a_hs", "bt565_a_clk",
                 "bt565_a_din0", "bt565_a_din1", "bt565_a_din2",
                 "bt565_a_din3", "bt565_a_din4", "bt565_a_din5",
                 "bt565_a_din6", "bt565_a_din7" ],

    "tsin_a": [ "tsin_a_valid", "tsin_a_sop", "tsin_a_din0", "tsin_a_clk" ],

    "tsin_b": ["tsin_b_valid_x", "tsin_b_sop_x", "tsin_b_din0_x", "tsin_b_clk_x",
                "tsin_b_valid_z", "tsin_b_sop_z", "tsin_b_din0_z", "tsin_b_clk_z",
                "tsin_b_fail", "tsin_b_din1", "tsin_b_din2", "tsin_b_din3",
                "tsin_b_din4", "tsin_b_din5", "tsin_b_din6", "tsin_b_din7" ],
    
    "hdmitx": [ "hdmitx_sda", "hdmitx_sck", "hdmitx_hpd_in" ],

    "pdm": [ "pdm_din0_c", "pdm_din1_c", "pdm_din2_c", "pdm_din3_c",
             "pdm_dclk_c",
             "pdm_din0_x", "pdm_din1_x", "pdm_din2_x", "pdm_din3_x",
             "pdm_dclk_x",
             "pdm_din0_z", "pdm_din1_z", "pdm_din2_z", "pdm_din3_z",
             "pdm_dclk_z",
             "pdm_din0_a", "pdm_din1_a", "pdm_din2_a", "pdm_din3_a",
             "pdm_dclk_a" ],

    "spdif_in": [ "spdif_in_h", "spdif_in_a10", "spdif_in_a12" ],

    "spdif_out": [ "spdif_out_h", "spdif_out_a11", "spdif_out_a13" ],

    "mclk0": [ "mclk0_a" ],

    "mclk1": [ "mclk1_x", "mclk1_z", "mclk1_a" ],

    "tdm_a": [ "tdm_a_slv_sclk", "tdm_a_slv_fs", "tdm_a_sclk", "tdm_a_fs",
               "tdm_a_din0", "tdm_a_din1", "tdm_a_dout0", "tdm_a_dout1" ],

    "tdm_b": [ "tdm_b_slv_sclk", "tdm_b_slv_fs", "tdm_b_sclk", "tdm_b_fs",
               "tdm_b_din0", "tdm_b_din1", "tdm_b_din2",
               "tdm_b_din3_a", "tdm_b_din3_h",
               "tdm_b_dout0", "tdm_b_dout1", "tdm_b_dout2",
               "tdm_b_dout3_a", "tdm_b_dout3_h" ],

    "tdm_c": [ "tdm_c_slv_sclk_a", "tdm_c_slv_fs_a",
               "tdm_c_slv_sclk_z", "tdm_c_slv_fs_z",
               "tdm_c_sclk_a", "tdm_c_fs_a",
               "tdm_c_sclk_z", "tdm_c_fs_z",
               "tdm_c_din0_a", "tdm_c_din1_a",
               "tdm_c_din2_a", "tdm_c_din3_a",
               "tdm_c_din0_z", "tdm_c_din1_z",
               "tdm_c_din2_z", "tdm_c_din3_z",
               "tdm_c_dout0_a", "tdm_c_dout1_a",
               "tdm_c_dout2_a", "tdm_c_dout3_a",
               "tdm_c_dout0_z", "tdm_c_dout1_z",
               "tdm_c_dout2_z", "tdm_c_dout3_z" ],
}

ao_function_to_group = {
    "gpio_aobus": [ "GPIOAO_0", "GPIOAO_1", "GPIOAO_2", "GPIOAO_3", "GPIOAO_4",
                    "GPIOAO_5", "GPIOAO_6", "GPIOAO_7", "GPIOAO_8", "GPIOAO_9",
                    "GPIOAO_10", "GPIOAO_11", "GPIOE_0", "GPIOE_1", "GPIOE_2" ],

    "uart_ao_a": [ "uart_ao_a_tx", "uart_ao_a_rx", "uart_ao_a_cts", "uart_ao_a_rts" ],

    "uart_ao_b": [ "uart_ao_b_tx_2", "uart_ao_b_rx_3",
                   "uart_ao_b_tx_8", "uart_ao_b_rx_9",
                   "uart_ao_b_cts", "uart_ao_b_rts" ],

    "i2c_ao": ["i2c_ao_sck", "i2c_ao_sda",
                "i2c_ao_sck_e", "i2c_ao_sda_e" ],
    
    "i2c_ao_slave": [ "i2c_ao_slave_sck", "i2c_ao_slave_sda" ],

    "remote_ao_input": [ "remote_ao_input" ],

    "remote_ao_out": [ "remote_ao_out" ],

    "pwm_a_e": [ "pwm_a_e" ],

    "pwm_ao_a": [ "pwm_ao_a", "pwm_ao_a_hiz" ],

    "pwm_ao_b": [ "pwm_ao_b" ],

    "pwm_ao_c": [ "pwm_ao_c_4", "pwm_ao_c_hiz", "pwm_ao_c_6" ],

    "pwm_ao_d": [ "pwm_ao_d_5", "pwm_ao_d_10", "pwm_ao_d_e" ],

    "jtag_a": [ "jtag_a_tdi", "jtag_a_tdo", "jtag_a_clk", "jtag_a_tms" ],

    "cec_ao_a": [ "cec_ao_a" ],

    "cec_ao_b": [ "cec_ao_b" ],

    "tsin_ao_a": [ "tsin_ao_asop", "tsin_ao_adin0", "tsin_ao_aclk", "tsin_ao_a_valid" ],

    "spdif_ao_out": [ "spdif_ao_out" ],

    "tdm_ao_b": [ "tdm_ao_b_dout0", "tdm_ao_b_dout1", "tdm_ao_b_dout2",
                  "tdm_ao_b_fs", "tdm_ao_b_sclk",
                  "tdm_ao_b_din0", "tdm_ao_b_din1", "tdm_ao_b_din2",
                  "tdm_ao_b_slv_fs", "tdm_ao_b_slv_sclk" ],

    "mclk0_ao": [ "mclk0_ao" ]
}

########################################################
# With the above information, it is enough to decode the DTS pinmux data,
# which is in the form: port: string -> function: string -> pad

import sys

if __name__ == "__main__":
    sys.stderr.write(sys.argv[0] + ": This script is not meant to be run, see create_pinctrl_config.py.")
