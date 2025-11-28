/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

// I2C header for the OpenTitan I2C IP block for the PULP Cheshire SoC in FAST mode (400KHz).
// Use this as a template for other device implementations using the same definitions.
// https://opentitan.org/book/hw/ip/i2c/doc/programmers_guide.html

#define I2C_CHESHIRE

/* Register definitions for Cheshire/Serengeti, accounting
 * for present hardware and IP version. */
typedef struct opentitan_i2c_regs {
    uint32_t intr_state;
    uint32_t intr_enable;
    uint32_t intr_test;
    uint32_t alert_test;
    uint32_t ctrl;
    uint32_t status;
    uint32_t rdata;
    uint32_t fdata;
    uint32_t fifo_ctrl;
    uint32_t host_fifo_status;
    uint32_t ovrd;
    uint32_t val;
    uint32_t timing0;
    uint32_t timing1;
    uint32_t timing2;
    uint32_t timing3;
    uint32_t timing4;
    uint32_t timeout_ctrl;
    uint32_t target_id;
    uint32_t acqdata;
    uint32_t txdata;
    uint32_t host_timeout_ctrl;
} opentitan_i2c_regs_t;

/* Timing properties for timing init algorithm */

// Input clock period (peripheral clocK)
#define T_CLK (20)      // SoC 50MHz clock is used directly for I2C(?) -> 50MHz^-1=20ns

// I2C speed mode
#define I2C_MODE_FAST

// Expected bus rise time in ns
#define T_RISE (150)     // Value from table 11 in I2C spec UM10204 rev7

// Expected bus fall time in ns
#define T_FALL (300)     // t_f = 20ns * (Vdd / 5.5V) -> Vdd = 3.3V

// SCL period in ns
#define SCL_PERIOD (2500)   // 400KHz target -> (400KHz)^-1 = 2500nS

#define I2C_MODE_FAST   // Select fast mode
#define DUTY_100X (32)

#define OPENTITAN_I2C_MAX_BUS_ADDRESS     ((1 << 7) - 1)

/* FIFO config */
#define I2C_FMT_THRESHOLD       (1) // Only refill when FIFO is empty.
#define I2C_RX_THRESHOLD        (0) // Extract as soon as data is available.

// Register definitions - these vary by version.

/* HW properties */
#define OPENTITAN_I2C_FIFO_DEPTH    (64)
#define OPENTITAN_I2C_READ_MAX      (64)

/*
 * Register fields.
 * We define every bit field as follows:
 * Offset: number of bits the mask is shifted from the LSB - used to make
 *          read fields readable.
 * Mask: mask of bits in the field, left-shifted by offset
 * Bit: mask of exact bit
 */

// TIMING0
// 0:15 -> THIGH, 16:31 -> TLOW
#define I2C_TIMING0_THIGH_MASK      (0xFFFF)
#define I2C_TIMING0_THIGH_OFFSET    (0x0)
#define I2C_TIMING0_TLOW_MASK       (0xFFFF0000)
#define I2C_TIMING0_TLOW_OFFSET     (16)

// TIMING1
// 0:15 -> T_R, 16:31 -> T_F
#define I2C_TIMING1_T_R_MASK        (0xFFFF)
#define I2C_TIMING1_T_R_OFFSET      (0x0)
#define I2C_TIMING1_T_F_MASK        (0xFFFF0000)
#define I2C_TIMING1_T_F_OFFSET      (16)

// TIMING2
// 0:15 -> TSU_STA, 16:31 -> THD_STA
#define I2C_TIMING2_TSU_STA_MASK    (0xFFFF)
#define I2C_TIMING2_TSU_STA_OFFSET  (0x0)
#define I2C_TIMING2_THD_STA_MASK    (0xFFFF0000)
#define I2C_TIMING2_THD_STA_OFFSET  (16)

// TIMING3
// 0:15 -> TSU_DAT, 16:31 -> THD_DAT
#define I2C_TIMING3_TSU_DAT_MASK    (0xFFFF)
#define I2C_TIMING3_TSU_DAT_OFFSET  (0x0)
#define I2C_TIMING3_THD_DAT_MASK    (0xFFFF0000)
#define I2C_TIMING3_THD_DAT_OFFSET  (16)

// TIMING4
// 0:15 -> TSU_STO, 16:31 -> T_BUF
#define I2C_TIMING4_TSU_STO_MASK    (0xFFFF)
#define I2C_TIMING4_TSU_STO_OFFSET  (0)
#define I2C_TIMING4_T_BUF_MASK      (0xFFFF0000)
#define I2C_TIMING4_T_BUF_OFFSET    (16)

// TIMEOUT_CTRL
// 0:30 -> VAL, 31 -> EN
#define I2C_TIMEOUT_CTRL_VAL_MASK   (0x7FFFFFFF)
#define I2C_TIMEOUT_CTRL_VAL_OFFSET (0)
#define I2C_TIMEOUT_CTRL_EN_BIT     (1 << 31)

// CTRL
// 0 -> enable host, 1 -> enable target, 2 -> LLPBK, 3 -> NACK_ADDR_AFTER_TIMEOUT, 4-> ACK_CTRL_EN,
// 5 -> MULTI_CONTROLLER_MONITOR_EN, 6 -> TX_STRETCH_CTRL_EN
#define I2C_CTRL_ENHOST_BIT         (0x1)
#define I2C_CTRL_ENTARGET_BIT       (0x2)
#define I2C_CTRL_LLPBK_BIT          (0x4)
// #define I2C_CTRL_NACK_ADDR_P_TIMEOUT_BIT       (0x8)
// #define I2C_CTRL_ACK_CTRL_EN_BIT    (0x10)
// #define I2C_CTRL_MULTI_CONTROLLER_MON_EN_BIT    (0x20)
// #define I2C_CTRL_TX_STRETCH_CTRL_EN_BIT         (0x30)

// STATUS
// 0 -> FMTFULL, 1 -> RXFULL, 2 -> FMTEMPTY, 3 -> HOSTIDLE,
// 4 -> TARGETIDLE, 5 -> RXEMPTY, 6 -> TXFULL, 7 -> ACQFULL,
// 8 -> TXEMPTY, 9 -> ACQEMPTY, 10 -> ACK_CTRL_STRETCH
#define I2C_STATUS_FMTFULL_BIT           (1 << 0)
#define I2C_STATUS_RXFULL_BIT            (1 << 1)
#define I2C_STATUS_FMTEMPTY_BIT          (1 << 2)
#define I2C_STATUS_HOSTIDLE_BIT          (1 << 3)
#define I2C_STATUS_TARGETIDLE_BIT        (1 << 4)
#define I2C_STATUS_RXEMPTY_BIT           (1 << 5)
#define I2C_STATUS_TXFULL_BIT            (1 << 6)
#define I2C_STATUS_ACQFULL_BIT           (1 << 7)
#define I2C_STATUS_TXEMPTY_BIT           (1 << 8)
#define I2C_STATUS_ACQEMPTY_BIT          (1 << 9)
#define I2C_STATUS_ACK_CTRL_STRETCH_BIT  (1 << 10)

// FDATA
// 0:7 -> data byte, 8 -> START bit, 9 -> STOP bit, 10 -> READB, 11 -> RCONT, 12 -> NAKOK
#define I2C_FDATA_FBYTE_MASK        (0xFF)
#define I2C_FDATA_FBYTE_OFFSET      (0)
#define I2C_FDATA_START_OFFSET      (8)
#define I2C_FDATA_STOP_OFFSET       (9)
#define I2C_FDATA_READB_OFFSET      (10)
#define I2C_FDATA_RCONT_OFFSET      (11)
#define I2C_FDATA_NAKOK_OFFSET      (12)
typedef struct _fdata_fmt_flags {
    uint32_t start; // Send start signal before next byte
    uint32_t stop; // Send stop signal after next byte (not valid if readb & rcont = 1)
    uint32_t readb; // Mark next byte to specify n. bytes to read instead of write
    uint32_t rcont; // If reading, request to continue reading after final byte of last read.
    uint32_t nakok; // Ignore target device NAKs for writes. Doesn't work with any reads.
} fdata_fmt_flags_t;

// FIFO_CTRL
// 0 -> RXRST, 1 -> FMTRST, 2:4 RXILVL, 5:6 -> FMTILVL, 7: ACQRST, 8 -> TXRST
#define I2C_FIFO_CTRL_RXRST_BIT     (0x1)
#define I2C_FIFO_CTRL_FMTRST_BIT    (0x2)

#define I2C_FIFO_CTRL_RXILVL_MASK    (0x1C)     // 0b1 1100
#define I2C_FIFO_CTRL_RXILVL_OFFSET  (0x2)
#define I2C_FIFO_CTRL_FMTILVL_MASK    (0x60)    // 0b110 0000
#define I2C_FIFO_CTRL_FMTILVL_OFFSET  (0x5)

#define I2C_FIFO_CTRL_ACQRST_BIT    (1 << 6)
#define I2C_FIFO_CTRL_TXRST_BIT     (1 << 7)

// FIFO_STATUS
// 0:6 -> FMTLVL, 8:14 -> TXLVL
#define I2C_FIFO_STATUS_FMTLVL_MASK     (0x7F)
#define I2C_FIFO_STATUS_FMTLVL_OFFSET   (0)
#define I2C_FIFO_STATUS_TXLVL_MASK      (0x7F00)
#define I2C_FIFO_STATUS_TXLVL_OFFSET    (8)
#define I2C_FIFO_STATUS_RXLVL_MASK      (0x7F0000)
#define I2C_FIFO_STATUS_RXLVL_OFFSET    (16)
#define I2C_FIFO_STATUS_ACQLVL_MASK     (0x7F000000)
#define I2C_FIFO_STATUS_ACQLVL_OFFSET   (24)

// INTR_STATE
// 0 -> FMT_THRESHOLD, 1 -> RX_THRESHOLD, 2 -> ACQ_THRESHOLD, 3 -> RX_OVERFLOW,
// 4 -> CONTROLLER_HALT, 5 -> SCL_INTERFERENCE, 6 -> SDA_INTERFERENCE, 7 -> STRETCH_TIMEOUT,
// 8 -> SDA_UNSTABLE, 9 -> CMD_COMPLETE, 10 -> TX_STRETCH, 11 -> TX_THRESHOLD,
// 12 -> ACQ_STRETCH, 13 -> UNEXP_STOP, 14 -> HOST_TIMEOUT
#define I2C_INTR_STATE_FMT_THRESHOLD_BIT    (1 << 0)
#define I2C_INTR_STATE_RX_THRESHOLD_BIT     (1 << 1)
#define I2C_INTR_STATE_FMT_OVERFLOW_BIT     (1 << 2)
#define I2C_INTR_STATE_RX_OVERFLOW_BIT      (1 << 3)
#define I2C_INTR_STATE_NAK_BIT              (1 << 4)
#define I2C_INTR_STATE_SCL_INTERFERENCE_BIT (1 << 5)
#define I2C_INTR_STATE_SDA_INTERFERENCE_BIT (1 << 6)
#define I2C_INTR_STATE_STRETCH_TIMEOUT_BIT  (1 << 7)
#define I2C_INTR_STATE_SDA_UNSTABLE_BIT     (1 << 8)
#define I2C_INTR_STATE_CMD_COMPLETE_BIT     (1 << 9)
#define I2C_INTR_STATE_TX_STRETCH_BIT       (1 << 10)
#define I2C_INTR_STATE_TX_OVERFLOW_BIT      (1 << 11)
#define I2C_INTR_STATE_ACQ_FULL_BIT         (1 << 12)
#define I2C_INTR_STATE_UNEXP_STOP_BIT       (1 << 13)
#define I2C_INTR_STATE_HOST_TIMEOUT_BIT     (1 << 14)

// INTR_TEST
// 0 -> FMT_THRESHOLD, 1 -> RX_THRESHOLD, 2 -> ACQ_THRESHOLD, 3 -> RX_OVERFLOW,
// 4 -> CONTROLLER_HALT, 5 -> SCL_INTERFERENCE, 6 -> SDA_INTERFERENCE, 7 -> STRETCH_TIMEOUT,
// 8 -> SDA_UNSTABLE, 9 -> CMD_COMPLETE, 10 -> TX_STRETCH, 11 -> TX_THRESHOLD,
// 12 -> ACQ_STRETCH, 13 -> UNEXP_STOP, 14 -> HOST_TIMEOUT
#define I2C_INTR_TEST_FMT_THRESHOLD_BIT    (1 << 0)
#define I2C_INTR_TEST_RX_THRESHOLD_BIT     (1 << 1)
#define I2C_INTR_TEST_ACQ_THRESHOLD_BIT    (1 << 2)
#define I2C_INTR_TEST_RX_OVERFLOW_BIT      (1 << 3)
#define I2C_INTR_TEST_CONTROLLER_HALT_BIT  (1 << 4)
#define I2C_INTR_TEST_SCL_INTERFERENCE_BIT (1 << 5)
#define I2C_INTR_TEST_SDA_INTERFERENCE_BIT (1 << 6)
#define I2C_INTR_TEST_STRETCH_TIMEOUT_BIT  (1 << 7)
#define I2C_INTR_TEST_SDA_UNSTABLE_BIT     (1 << 8)
#define I2C_INTR_TEST_CMD_COMPLETE_BIT     (1 << 9)
#define I2C_INTR_TEST_TX_STRETCH_BIT       (1 << 10)
#define I2C_INTR_TEST_TX_THRESHOLD_BIT     (1 << 11)
#define I2C_INTR_TEST_ACQ_STRETCH_BIT      (1 << 12)
#define I2C_INTR_TEST_UNEXP_STOP_BIT       (1 << 13)
#define I2C_INTR_TEST_HOST_TIMEOUT_BIT     (1 << 14)

// INTR_ENABLE
// 0 -> FMT_THRESHOLD, 1 -> RX_THRESHOLD, 2 -> ACQ_THRESHOLD, 3 -> RX_OVERFLOW,
// 4 -> CONTROLLER_HALT, 5 -> SCL_INTERFERENCE, 6 -> SDA_INTERFERENCE, 7 -> STRETCH_TIMEOUT,
// 8 -> SDA_UNSTABLE, 9 -> CMD_COMPLETE, 10 -> TX_STRETCH, 11 -> TX_THRESHOLD,
// 12 -> ACQ_STRETCH, 13 -> UNEXP_STOP, 14 -> HOST_TIMEOUT
#define I2C_INTR_ENABLE_FMT_THRESHOLD_BIT    (1 << 0)
#define I2C_INTR_ENABLE_RX_THRESHOLD_BIT     (1 << 1)
#define I2C_INTR_ENABLE_FMT_OVERFLOW_BIT     (1 << 2)
#define I2C_INTR_ENABLE_RX_OVERFLOW_BIT      (1 << 3)
#define I2C_INTR_ENABLE_NAK_BIT              (1 << 4)
#define I2C_INTR_ENABLE_SCL_INTERFERENCE_BIT (1 << 5)
#define I2C_INTR_ENABLE_SDA_INTERFERENCE_BIT (1 << 6)
#define I2C_INTR_ENABLE_STRETCH_TIMEOUT_BIT  (1 << 7)
#define I2C_INTR_ENABLE_SDA_UNSTABLE_BIT     (1 << 8)
#define I2C_INTR_ENABLE_CMD_COMPLETE_BIT     (1 << 9)
#define I2C_INTR_ENABLE_TX_STRETCH_BIT       (1 << 10)
#define I2C_INTR_ENABLE_TX_OVERFLOW_BIT      (1 << 11)
#define I2C_INTR_ENABLE_ACQ_FULL_BIT         (1 << 12)
#define I2C_INTR_ENABLE_UNEXP_STOP_BIT       (1 << 13)
#define I2C_INTR_ENABLE_HOST_TIMEOUT_BIT     (1 << 14)
