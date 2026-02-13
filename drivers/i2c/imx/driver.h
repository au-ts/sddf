#include <sddf/i2c/i2c_driver.h>
#include "gpio.h"
#include "clk.h"
#pragma once
// TODO: might need to change this all to little endian

// Ctl register fields
#define REG_CTRL_IEN (BIT(7))
#define REG_CTRL_MSTA (BIT(5))

// Status register fields
#define REG_STAT_MTX (BIT(4))
// Busy bit for bus
#define REG_STAT_IBB (BIT(5))
#define REG_STAT_IFF (BIT(1))
#define REG_STAT_RXAK (BIT(0))
#define REG_STAT_TXAK (BIT(3))
