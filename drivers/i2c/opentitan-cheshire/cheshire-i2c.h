/*
 * Copyright 2024, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

// I2C header for the OpenTitan I2C IP block for the PULP Cheshire SoC in FAST mode (400KHz).
// Use this as a template for other device implementations using the same definitions.
// https://opentitan.org/book/hw/ip/i2c/doc/programmers_guide.html
// Matt Rossouw (matthew.rossouw@unsw.edu.au)
// 01/2025

/* Register definitions */
#define I2C_BASE_ADDR        0x03003000

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
#define I2C_HOST_NACK_HANDLER_TIMEOUT (I2C_BASE_ADDR + 0x74) // Host-Mode NACK timeout
#define I2C_CONTROLLER_EVENTS       (I2C_BASE_ADDR + 0x78)  // Controller halt event flags
#define I2C_TARGET_EVENTS           (I2C_BASE_ADDR + 0x7c)  // Target clock stretch event flags

/* Timing properties for timing init algorithm */

// Input clock period (peripheral clocK)
#define T_CLK (20)      // SoC 50MHz clock is used directly for I2C(?) -> 50MHz^-1=20ns

// I2C speed mode
#define SPEED_MODE (I2C_SPEED_FAST)

// Expected bus rise time in ns
#define T_RISE (50)     // Note: this is an optimistic and "guesstimated" value

// Expected bus fall time in ns
#define T_FALL (120)    // Value from table 10 in I2C spec UM10204 rev7

// SCL period in ns
#define SCL_PERIOD (2500)   // 400KHz target -> (400KHz)^-1 = 2500nS

#define I2C_MODE_FAST   // Select fast mode
