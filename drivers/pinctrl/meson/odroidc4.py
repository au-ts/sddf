# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

# Document referenced: Linux: drivers/pinctrl/meson/pinctrl-meson-g12a.c

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

# Second and main GPIO chip
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


}

########################################################
# To represent the above in hardware, each pad has a 3 bits integer mux value.
# To indicate what port it is muxed to.
# All pads are assigned function 0 by default, then these values override it.

port_to_mux_func = {
    "emmc_nand_d0": 1,
    "emmc_nand_d1": 1,
    "emmc_nand_d2": 1,
    "emmc_nand_d3": 1,
    "emmc_nand_d4": 1,
    "emmc_nand_d5": 1,
    "emmc_nand_d6": 1,
    "emmc_nand_d7": 1,
    "emmc_clk":     1,
    "emmc_cmd":     1,
    "emmc_nand_ds": 1,
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

    "tsin_b": [	"tsin_b_valid_x", "tsin_b_sop_x", "tsin_b_din0_x", "tsin_b_clk_x",
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
    
    "gpio_aobus": [ "GPIOAO_0", "GPIOAO_1", "GPIOAO_2", "GPIOAO_3", "GPIOAO_4",
                    "GPIOAO_5", "GPIOAO_6", "GPIOAO_7", "GPIOAO_8", "GPIOAO_9",
                    "GPIOAO_10", "GPIOAO_11", "GPIOE_0", "GPIOE_1", "GPIOE_2" ],

    "uart_ao_a": [ "uart_ao_a_tx", "uart_ao_a_rx", "uart_ao_a_cts", "uart_ao_a_rts" ],

    "uart_ao_b": [ "uart_ao_b_tx_2", "uart_ao_b_rx_3",
                   "uart_ao_b_tx_8", "uart_ao_b_rx_9",
                   "uart_ao_b_cts", "uart_ao_b_rts" ],

    "i2c_ao": [	"i2c_ao_sck", "i2c_ao_sda",
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
# which is in the form: port: string -> function: string
