// audio.h - Meson S905X3 (ODROID C4)

#pragma once
#include <stdint.h>

#define AUDIO_BASE 0xff660000

// #### CLOCK GATE REGISTERS ####
// Audio clock gate register 0
#define EE_AUDIO_CLK_GATE_EN0_ADDR AUDIO_BASE + 0x00
#define EE_AUDIO_CLK_GATE_EN0 (*(volatile uint32_t *)(EE_AUDIO_CLK_GATE_EN0_ADDR))

// Bits we care about for I2S / TDM
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_LKR BIT(28)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_RES_B_EN BIT(26)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_RES_A_EN BIT(18)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_LOOPBACK_A BIT(15)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_FRDDR_C BIT(11)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_FRDDR_B BIT(10)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_FRDDR_A BIT(9)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_TDMOUT_C BIT(8)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_TDMOUT_C BIT(7)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_TDMOUT_A BIT(6)
#define EE_AUDIO_CLK_GATE_EN0_AUDIO_DDR_ARB BIT(0)

// Audio clock gate register 1
#define EE_AUDIO_CLK_GATE_EN1_ADDR AUDIO_BASE + 0x01
#define EE_AUDIO_CLK_GATE_EN1 (*(volatile uint32_t *)(EE_AUDIO_CLK_GATE_EN1_ADDR))

// Bits we care about for I2S / TDM
#define EE_AUDIO_CLK_GATE_EN1_LOOPBACK_B BIT(2)
#define EE_AUDIO_CLK_GATE_EN1_FRDDR_D BIT(0)

// ####  MASTER CLOCK CONTROL REGISTERS ####
// Audio clock A-D control registers. All are identical
#define EE_AUDIO_MCLK_A_CTRL_ADDR AUDIO_BASE + 0x02
#define EE_AUDIO_MCLK_A_CTRL (*(volatile uint32_t *)(EE_AUDIO_MCLK_A_CTRL_ADDR))

#define EE_AUDIO_MCLK_B_CTRL_ADDR AUDIO_BASE + 0x03
#define EE_AUDIO_MCLK_B_CTRL (*(volatile uint32_t *)(EE_AUDIO_MCLK_B_CTRL_ADDR))

#define EE_AUDIO_MCLK_C_CTRL_ADDR AUDIO_BASE + 0x04
#define EE_AUDIO_MCLK_C_CTRL (*(volatile uint32_t *)(EE_AUDIO_MCLK_C_CTRL_ADDR))

#define EE_AUDIO_MCLK_D_CTRL_ADDR AUDIO_BASE + 0x05
#define EE_AUDIO_MCLK_D_CTRL (*(volatile uint32_t *)(EE_AUDIO_MCLK_D_CTRL_ADDR))

#define EE_AUDIO_MCLK_E_CTRL_ADDR AUDIO_BASE + 0x06
#define EE_AUDIO_MCLK_E_CTRL (*(volatile uint32_t *)(EE_AUDIO_MCLK_E_CTRL_ADDR))

#define EE_AUDIO_MCLK_F_CTRL_ADDR AUDIO_BASE + 0x07
#define EE_AUDIO_MCLK_F_CTRL (*(volatile uint32_t *)(EE_AUDIO_MCLK_F_CTRL_ADDR))

// Bits for ALL master clock control registers
#define EE_AUDIO_MCLK_CTRL_EN BIT(31)
#define EE_AUDIO_MCLK_CTRL_FRC_OSCIN BIT(30)
#define EE_AUDIO_MCLK_CTRL_CLK_SEL BIT(24) | BIT(25) | BIT(26) // See options defines below
#define EE_AUDIO_MCLK_CTRL_CLK_DIV 0xFF  // Sets MCLK clock divider. mclk_freq = pll_freq / clk_div

// MCLK_CLK_SEL options for EE_AUDIO_MCLK_X_CTRL_CLK_SEL
#define EE_AUDIO_MCLK_SEL_MP0_PLL 0
#define EE_AUDIO_MCLK_SEL_MP1_PLL 1
#define EE_AUDIO_MCLK_SEL_MP2_PLL 2
#define EE_AUDIO_MCLK_SEL_MP3_PLL 3
#define EE_AUDIO_MCLK_SEL_HIFI_PLL 4
#define EE_AUDIO_MCLK_SEL_FCLK_DIV3 5   // 666MHz
#define EE_AUDIO_MCLK_SEL_FCLK_DIV4 6   // 500MHz
#define EE_AUDIO_MCLK_SEL_FCLK_DIV5 7   // 400MHz



// #### FRDDR REGISTERS BY INDEX ####
// for programatic usage of all registers. Same as
// FRDDR_A; offset by REG_ID_OFFSET repeatedly for B, C and D.
#define FRDDR_REG_ID_OFFSET                0x010
#define FRDDR_REG_CTRL0                    0x070
#define FRDDR_REG_CTRL1                    0x071
#define FRDDR_REG_START_ADDR               0x072
#define FRDDR_REG_FINISH_ADDR              0x073
#define FRDDR_REG_INT_ADDR                 0x074
#define FRDDR_REG_STATUS1                  0x075
#define FRDDR_REG_STATUS2                  0x076
#define FRDDR_REG_START_ADDRB              0x077
#define FRDDR_REG_FINISH_ADDRB             0x078
#define FRDDR_REG_INIT_ADDR                0x079
#define FRDDR_REG_CTRL2                    0x07a

// FRDDR CTRL register bits
#define FRDDR_REG_CTRL0_EN                (1<<31)
#define FRDDR_REG_CTRL0_PP_MD             (1<<30)
#define FRDDR_REG_CTRL0_ENDIAN  BIT(26) | BIT(25) | BIT(24)
#define FRDDR_REG_CTRL0_INT_EN          (0xFF << 16)
#define FRDDR_REG_CTRL0_ACK_DLY         (0xF << 12)
#define FRDDR_REG_CTRL0_BUS_UGT            BIT(0)

#define FRDDR_REG_CTRL1_FIFO_DEPTH      (0xFF << 24)
#define FRDDR_REG_CTRL1_START_WR_TH     (0xFF << 16)
#define FRDDR_REG_CTRL1_FORCE_FINISH        BIT(12)
#define FRDDR_REG_CTRL1_STATUS_SEL      (0xF << 8)
#define FRDDR


// #### FRDDR REGISTERS AND BITS ####
// There are far too many; taken from Amlogic Linux driver
#define EE_AUDIO_FRDDR_A_CTRL0             0x070
#define EE_AUDIO_FRDDR_A_CTRL1             0x071
#define EE_AUDIO_FRDDR_A_START_ADDR        0x072
#define EE_AUDIO_FRDDR_A_FINISH_ADDR       0x073
#define EE_AUDIO_FRDDR_A_INT_ADDR          0x074
#define EE_AUDIO_FRDDR_A_STATUS1           0x075
#define EE_AUDIO_FRDDR_A_STATUS2           0x076
#define EE_AUDIO_FRDDR_A_START_ADDRB       0x077
#define EE_AUDIO_FRDDR_A_FINISH_ADDRB      0x078
#define EE_AUDIO_FRDDR_A_INIT_ADDR         0x079
#define EE_AUDIO_FRDDR_A_CTRL2             0x07a

#define EE_AUDIO_FRDDR_B_CTRL0             0x080
#define EE_AUDIO_FRDDR_B_CTRL1             0x081
#define EE_AUDIO_FRDDR_B_START_ADDR        0x082
#define EE_AUDIO_FRDDR_B_FINISH_ADDR       0x083
#define EE_AUDIO_FRDDR_B_INT_ADDR          0x084
#define EE_AUDIO_FRDDR_B_STATUS1           0x085
#define EE_AUDIO_FRDDR_B_STATUS2           0x086
#define EE_AUDIO_FRDDR_B_START_ADDRB       0x087
#define EE_AUDIO_FRDDR_B_FINISH_ADDRB      0x088
#define EE_AUDIO_FRDDR_B_INIT_ADDR         0x089
#define EE_AUDIO_FRDDR_B_CTRL2             0x08a

#define EE_AUDIO_FRDDR_C_CTRL0             0x090
#define EE_AUDIO_FRDDR_C_CTRL1             0x091
#define EE_AUDIO_FRDDR_C_START_ADDR        0x092
#define EE_AUDIO_FRDDR_C_FINISH_ADDR       0x093
#define EE_AUDIO_FRDDR_C_INT_ADDR          0x094
#define EE_AUDIO_FRDDR_C_STATUS1           0x095
#define EE_AUDIO_FRDDR_C_STATUS2           0x096
#define EE_AUDIO_FRDDR_C_START_ADDRB       0x097
#define EE_AUDIO_FRDDR_C_FINISH_ADDRB      0x098
#define EE_AUDIO_FRDDR_C_INIT_ADDR         0x099
#define EE_AUDIO_FRDDR_C_CTRL2             0x09a