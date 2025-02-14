/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// OpenTitan I2C generic header. This file contains all OpenTitan specific definitions.

#pragma once

#include <cstdint>
#include <stdint.h>
#include <stdbool.h>

typedef struct i2c_timing_params {
    uint32_t t_high_min;
    uint32_t t_low_min;
    uint32_t t_hd_sta_min;
    uint32_t t_su_sta_min;
    uint32_t t_hd_dat_min;
    uint32_t t_su_dat_min;
    uint32_t t_buf_min;
    uint32_t t_sto_min;
    uint32_t t_r;
    uint32_t t_f;
    uint32_t t_h;
    uint32_t t_l;
} i2c_timing_params_t;

#define KILO (1000)
#define MEGA (1000000)

/* I2C speed modes in Hz */
enum I2C_SPEED_MODE {
    I2C_SPEED_STD = (100 * KILO),
    I2C_SPEED_FAST = (400 * KILO),
    I2C_SPEED_FASTPLUS = (1 * MEGA)
};

/* Fast mode settings */
#ifdef I2C_MODE_FAST
// Constants from Fast Mode in I2C spec (all in ns)
#define T_HIGH_MIN (600)    // SCL High period
#define T_LOW_MIN (1350)    // SCL Low period
#define T_HD_STA_MIN (600)  // Hold time (repeated) start condition
#define T_SU_STA_MIN (600)  // Set up time for a repeated start condition
#define T_HD_DAT_MIN (0)    // Data hold time (undefined for I2C! only needed for CBUS etc.)
#define T_SU_DAT_MIN (100)  // Data set up time
#define T_BUF_MIN (1300)    // Bus free time between start and stop
#define T_SU_STO_MIN (600)  // Set up time for a stop condition
                            // NOTE: the OpenTitan docs refer to just T_STO_min not this?
#define I2C_SCL_MAX_FREQ (I2C_SPEED_FAST)
#define I2C_SCL_MIN_T (2500)    // Min period in nanoseconds (max frequency) -> 400kHz^-1 = 2500ns
#endif

/* HW properties */
#define OPENTITAN_I2C_FIFO_DEPTH    (64)
#define OPENTITAN_I2C_READ_MAX      (64)

/* Register definitions */
// NOTE: I2C_BASE_ADDR must be defined by device_i2c.h for target platform.
#define I2C_INTR_STATE              (I2C_BASE_ADDR + 0x0)   // Interrupt State Register
#define I2C_INTR_ENABLE             (I2C_BASE_ADDR + 0x4)   // Interrupt Enable Register
#define I2C_INTR_TEST               (I2C_BASE_ADDR + 0x8)   // Interrupt Test Register
#define I2C_ALERT_TEST              (I2C_BASE_ADDR + 0xc)   // Alert Test Register
#define I2C_CTRL                    (I2C_BASE_ADDR + 0x10)  // I2C Control Register
#define I2C_STATUS                  (I2C_BASE_ADDR + 0x14)  // I2C Live Status Register
#define I2C_RDATA                   (I2C_BASE_ADDR + 0x18)  // I2C Read Data
#define I2C_FDATA                   (I2C_BASE_ADDR + 0x1c)  // I2C Host Format Data
#define I2C_FIFO_CTRL               (I2C_BASE_ADDR + 0x20)  // I2C FIFO control register
#define I2C_HOST_FIFO_CONFIG        (I2C_BASE_ADDR + 0x24)  // Host mode FIFO configuration
#define I2C_TARGET_FIFO_CONFIG      (I2C_BASE_ADDR + 0x28)  // Target mode FIFO configuration
#define I2C_HOST_FIFO_STATUS        (I2C_BASE_ADDR + 0x2c)  // Host mode FIFO status register
#define I2C_TARGET_FIFO_STATUS      (I2C_BASE_ADDR + 0x30)  // Target mode FIFO status register
#define I2C_OVRD                    (I2C_BASE_ADDR + 0x34)  // I2C Override Control Register
#define I2C_VAL                     (I2C_BASE_ADDR + 0x38)  // Oversampled RX values
#define I2C_TIMING0                 (I2C_BASE_ADDR + 0x3c)  // Detailed I2C Timing 0
#define I2C_TIMING1                 (I2C_BASE_ADDR + 0x40)  // Detailed I2C Timing 1
#define I2C_TIMING2                 (I2C_BASE_ADDR + 0x44)  // Detailed I2C Timing 2
#define I2C_TIMING3                 (I2C_BASE_ADDR + 0x48)  // Detailed I2C Timing 3
#define I2C_TIMING4                 (I2C_BASE_ADDR + 0x4c)  // Detailed I2C Timing 4
#define I2C_TIMEOUT_CTRL            (I2C_BASE_ADDR + 0x50)  // Clock stretching and bus timeout
#define I2C_TARGET_ID               (I2C_BASE_ADDR + 0x54)  // I2C target address and mask pairs
#define I2C_ACQDATA                 (I2C_BASE_ADDR + 0x58)  // I2C target acquired data
#define I2C_TXDATA                  (I2C_BASE_ADDR + 0x5c)  // I2C target transmit data
#define I2C_HOST_TIMEOUT_CTRL       (I2C_BASE_ADDR + 0x60)  // Host clock generation timeout
#define I2C_TARGET_TIMEOUT_CTRL     (I2C_BASE_ADDR + 0x64)  // Target internal stretching timeout
#define I2C_TARGET_NACK_COUNT       (I2C_BASE_ADDR + 0x68)  // Target NACK count
#define I2C_TARGET_ACK_CTRL         (I2C_BASE_ADDR + 0x6c)  // Mid-transfer (N)ACK phase handling
#define I2C_ACQ_FIFO_NEXT_DATA      (I2C_BASE_ADDR + 0x70)  // Pending ACQ FIFO data byte
#define I2C_HOST_NACK_HANDLER_TIMEOUT (I2C_BASE_ADDR + 0x74)// Host-Mode NACK timeout
#define I2C_CONTROLLER_EVENTS       (I2C_BASE_ADDR + 0x78)  // Controller halt event flags
#define I2C_TARGET_EVENTS           (I2C_BASE_ADDR + 0x7c)  // Target clock stretch event flags

/* Register fields */

// TIMING0
#define I2C_TIMING0_THIGH_MASK      (0x1FFF)
#define I2C_TIMING0_THIGH_OFFSET    (0x0)
#define I2C_TIMING0_TLOW_MASK       (0x1FFF0000)
#define I2C_TIMING0_TLOW_OFFSET     (16)

// TIMING1
// 0:9 -> T_R, 16:24 -> T_F
#define I2C_TIMING1_T_R_MASK        (0x03FF)
#define I2C_TIMING1_T_R_OFFSET      (0x0)
#define I2C_TIMING1_T_F_MASK        (0x1FF0000)
#define I2C_TIMING1_T_F_OFFSET      (16)

// TIMING2
// 0:12 -> TSU_STA, 16:28 -> THD_STA
#define I2C_TIMING2_TSU_STA_MASK    (0x1FFF)
#define I2C_TIMING2_TSU_STA_OFFSET  (0x0)
#define I2C_TIMING2_THD_STA_MASK    (0x1FFF0000)
#define I2C_TIMING2_THD_STA_OFFSET  (16)

// TIMING3
// 0:8 -> TSU_DAT, 16:28 -> THD_DAT
#define I2C_TIMING3_TSU_DAT_MASK    (0x1FF)
#define I2C_TIMING3_TSU_DAT_OFFSET  (0x0)
#define I2C_TIMING3_THD_DAT_MASK    (0x1FFF0000)
#define I2C_TIMING3_THD_DAT_OFFSET  (16)

// TIMING4
// 0:12 -> TSU_STO, 16:28 -> T_BUF
#define I2C_TIMING4_TSU_STO_MASK    (0x1FFF)
#define I2C_TIMING4_TSU_STO_OFFSET  (0)
#define I2C_TIMING4_T_BUF_MASK      (0x1FFF0000)
#define I2C_TIMING4_T_BUF_OFFSET    (16)

// CTRL
// 0 -> enable host, 1 -> enable target, 2 -> LLPBK, 3 -> NACK_ADDR_AFTER_TIMEOUT, 4-> ACK_CTRL_EN,
// 5 -> MULTI_CONTROLLER_MONITOR_EN, 6 -> TX_STRETCH_CTRL_EN
#define I2C_CTRL_ENHOST_MASK        (0x1)
#define I2C_CTRL_ENHOST_OFFSET      (0)
#define I2C_CTRL_ENTARGET_MASK      (0x2)
#define I2C_CTRL_ENTARGET_OFFSET    (1)
#define I2C_CTRL_LLPBK_MASK         (0x4)
#define I2C_CTRL_LLPBK_OFFSET       (2)
#define I2C_CTRL_NACK_ADDR_P_TIMEOUT_MASK       (0x8)
#define I2C_CTRL_NACK_ADDR_P_TIMEOUT_OFFSET     (3)
#define I2C_CTRL_ACK_CTRL_EN_MASK   (0x10)
#define I2C_CTRL_ACK_CTRL_EN_OFFSET (4)
#define I2C_CTRL_MULTI_CONTROLLER_MON_EN_MASK   (0x20)
#define I2C_CTRL_MULTI_CONTROLLER_MON_EN_OFFSET (5)
#define I2C_CTRL_TX_STRETCH_CTRL_EN_MASK        (0x30)
#define I2C_CTRL_TX_STRETCH_CTRL_EN_OFFSET      (6)

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
    uint32_t stop;  // Send stop signal after next byte (not valid if readb & rcont = 1)
    uint32_t readb; // Mark next byte to specify n. bytes to read instead of write
    uint32_t rcont; // If reading, request to continue reading after final byte of last read.
    uint32_t nakok; // Ignore target device NAKs for writes. Doesn't work with any reads.
} fdata_fmt_flags_t;

// HOST_FIFO_STATUS
// 0:11 -> FMTLVL, 16:27 -> RXLVL
#define I2C_HOST_FIFO_STATUS_FMTLVL_MASK    (0xFFF)
#define I2C_HOST_FIFO_STATUS_FMTLVL_OFFSET  (0)
#define I2C_HOST_FIFO_STATUS_RXLVL_MASK    (0xFFF)
#define I2C_HOST_FIFO_STATUS_RXLVL_OFFSET  (16)

// HOST_FIFO_CONFIG
// 0:11 -> RX_THRESH, 16:27 -> FMT_THRESH
#define I2C_HOST_FIFO_CONFIG_RXTHRESH_MASK  (0xFFF)
#define I2C_HOST_FIFO_CONFIG_RXTHRESH_OFFSET    (0)
#define I2C_HOST_FIFO_CONFIG_FMTTHRESH_MASK (0xFFF)
#define I2C_HOST_FIFO_CONFIG_FMTTHRESH_OFFSET   (16)

// INTR_STATE
// 0 -> FMT_THRESHOLD, 1 -> RX_THRESHOLD, 2 -> ACQ_THRESHOLD, 3 -> RX_OVERFLOW,
// 4 -> CONTROLLER_HALT, 5 -> SCL_INTERFERENCE, 6 -> SDA_INTERFERENCE, 7 -> STRETCH_TIMEOUT,
// 8 -> SDA_UNSTABLE, 9 -> CMD_COMPLETE, 10 -> TX_STRETCH, 11 -> TX_THRESHOLD,
// 12 -> ACQ_STRETCH, 13 -> UNEXP_STOP, 14 -> HOST_TIMEOUT
#define I2C_INTR_STATE_FMT_THRESHOLD_BIT    (1 << 0)
#define I2C_INTR_STATE_RX_THRESHOLD_BIT     (1 << 1)
#define I2C_INTR_STATE_ACQ_THRESHOLD_BIT    (1 << 2)
#define I2C_INTR_STATE_RX_OVERFLOW_BIT      (1 << 3)
#define I2C_INTR_STATE_CONTROLLER_HALT_BIT  (1 << 4)
#define I2C_INTR_STATE_SCL_INTERFERENCE_BIT (1 << 5)
#define I2C_INTR_STATE_SDA_INTERFERENCE_BIT (1 << 6)
#define I2C_INTR_STATE_STRETCH_TIMEOUT_BIT  (1 << 7)
#define I2C_INTR_STATE_SDA_UNSTABLE_BIT     (1 << 8)
#define I2C_INTR_STATE_CMD_COMPLETE_BIT     (1 << 9)
#define I2C_INTR_STATE_TX_STRETCH_BIT       (1 << 10)
#define I2C_INTR_STATE_TX_THRESHOLD_BIT     (1 << 11)
#define I2C_INTR_STATE_ACQ_STRETCH_BIT      (1 << 12)
#define I2C_INTR_STATE_UNEXP_STOP_BIT       (1 << 13)
#define I2C_INTR_STATE_HOST_TIMEOUT         (1 << 14)

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
#define I2C_INTR_ENABLE_ACQ_THRESHOLD_BIT    (1 << 2)
#define I2C_INTR_ENABLE_RX_OVERFLOW_BIT      (1 << 3)
#define I2C_INTR_ENABLE_CONTROLLER_HALT_BIT  (1 << 4)
#define I2C_INTR_ENABLE_SCL_INTERFERENCE_BIT (1 << 5)
#define I2C_INTR_ENABLE_SDA_INTERFERENCE_BIT (1 << 6)
#define I2C_INTR_ENABLE_STRETCH_TIMEOUT_BIT  (1 << 7)
#define I2C_INTR_ENABLE_SDA_UNSTABLE_BIT     (1 << 8)
#define I2C_INTR_ENABLE_CMD_COMPLETE_BIT     (1 << 9)
#define I2C_INTR_ENABLE_TX_STRETCH_BIT       (1 << 10)
#define I2C_INTR_ENABLE_TX_THRESHOLD_BIT     (1 << 11)
#define I2C_INTR_ENABLE_ACQ_STRETCH_BIT      (1 << 12)
#define I2C_INTR_ENABLE_UNEXP_STOP_BIT       (1 << 13)
#define I2C_INTR_ENABLE_HOST_TIMEOUT_BIT     (1 << 14)

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

// CONTROLLER_EVENTS
// 0 -> NACK, 1 -> UNHANDLED_NACK_TIMEOUT, 2 -> BUS_TIMEOUT, 3 -> ARBITRATION_LOST
#define I2C_CONTROLLER_EVENTS_NACK_BIT                     (1 << 0)
#define I2C_CONTROLLER_EVENTS_UNHANDLED_NACK_TIMEOUT_BIT   (1 << 1)
#define I2C_CONTROLLER_EVENTS_BUS_TIMEOUT_BIT              (1 << 2)
#define I2C_CONTROLLER_EVENTS_ARBITRATION_LOST_BIT         (1 << 3)
