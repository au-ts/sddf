/*
 * Copyright 2024, UNSW
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
    // Not present in Cheshire
    // uint32_t intr_state;                    // 0x00: Interrupt State Register
    // uint32_t intr_enable;                   // 0x04: Interrupt Enable Register
    // uint32_t intr_test;                     // 0x08: Interrupt Test Register
    // uint32_t alert_test;                    // 0x0C: Alert Test Register
    uint32_t ctrl;                          // 0x10: I2C Control Register
    uint32_t status;                        // 0x14: I2C Live Status Register
    uint32_t rdata;                         // 0x18: I2C Read Data
    uint32_t fdata;                         // 0x1C: I2C Host Format Data
    uint32_t fifo_ctrl;                     // 0x20: I2C FIFO control register
    // uint32_t host_fifo_config;              // 0x24: Host mode FIFO configuration
    // uint32_t target_fifo_config;            // 0x28: Target mode FIFO configuration
    uint32_t host_fifo_status;              // 0x2C: Host mode FIFO status register
    // uint32_t target_fifo_status;            // 0x30: Target mode FIFO status register
    uint32_t ovrd;                          // 0x34: I2C Override Control Register
    uint32_t val;                           // 0x38: Oversampled RX values
    uint32_t timing0;                       // 0x3C: Detailed I2C Timing 0
    uint32_t timing1;                       // 0x40: Detailed I2C Timing 1
    uint32_t timing2;                       // 0x44: Detailed I2C Timing 2
    uint32_t timing3;                       // 0x48: Detailed I2C Timing 3
    uint32_t timing4;                       // 0x4C: Detailed I2C Timing 4
    uint32_t timeout_ctrl;                  // 0x50: Clock stretching and bus timeout
    uint32_t target_id;                     // 0x54: I2C target address and mask pairs
    uint32_t acqdata;                       // 0x58: I2C target acquired data
    uint32_t txdata;                        // 0x5C: I2C target transmit data
    uint32_t host_timeout_ctrl;             // 0x60: Host clock generation timeout
    // uint32_t target_timeout_ctrl;           // 0x64: Target internal stretching timeout
    // uint32_t target_nack_count;             // 0x68: Target NACK count
    // uint32_t target_ack_ctrl;               // 0x6C: Mid-transfer (N)ACK phase handling
    // uint32_t acq_fifo_next_data;            // 0x70: Pending ACQ FIFO data byte
    // uint32_t host_nack_handler_timeout;     // 0x74: Host-Mode NACK timeout
    // // Unused in Cheshire below this point
    // uint32_t controller_host_events;        // 0x78: Controller halt event flags
    // uint32_t target_events;                 // 0x7c: Target clock stretch event flags
} opentitan_i2c_regs_t;



/* Timing properties for timing init algorithm */

// Input clock period (peripheral clocK)
#define T_CLK (20)      // SoC 50MHz clock is used directly for I2C(?) -> 50MHz^-1=20ns

// I2C speed mode
#define I2C_MODE_FAST

// Expected bus rise time in ns
#define T_RISE (30)     // Value from table 11 in I2C spec UM10204 rev7

// Expected bus fall time in ns
#define T_FALL (12)     // t_f = 20ns * (Vdd / 5.5V) -> Vdd = 3.3V

// SCL period in ns
#define SCL_PERIOD (2500)   // 400KHz target -> (400KHz)^-1 = 2500nS

#define I2C_MODE_FAST   // Select fast mode
#define DUTY_100X 46    // 46% duty cycle * 100 for neater arithmetic

#define OPENTITAN_I2C_MAX_BUS_ADDRESS     (1 << 7)

/* FIFO config */
#define I2C_FMT_THRESHOLD       (1) // Only refill when FIFO is empty.
#define I2C_RX_THRESHOLD        (0) // Extract as soon as data is available.
