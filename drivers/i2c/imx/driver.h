/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sddf/i2c/i2c_driver.h>
#include <stdint.h>

// Base: 0x30A20000 for I2C1
struct imx_i2c_regs {
    uint16_t iadr;      // 0x00 - I2C Address Register
    uint16_t _pad0;
    uint16_t ifdr;      // 0x04 - I2C Frequency Divider Register
    uint16_t _pad1;
    uint16_t i2cr;      // 0x08 - I2C Control Register
    uint16_t _pad2;
    uint16_t i2sr;      // 0x0C - I2C Status Register
    uint16_t _pad3;
    uint16_t i2dr;      // 0x10 - I2C Data I/O Register
    uint16_t _pad4;
};

// I2CR Control Register bits
#define REG_CR_IEN      (1 << 7)    // I2C Enable
#define REG_CR_IIEN     (1 << 6)    // I2C Interrupt Enable
#define REG_CR_MSTA     (1 << 5)    // Master/Slave mode (1=Master, generates START when 0->1)
#define REG_CR_MTX      (1 << 4)    // Transmit/Receive (1=Transmit, 0=Receive)
#define REG_CR_TXAK     (1 << 3)    // Transmit Acknowledge (1=No ACK sent)
#define REG_CR_RSTA     (1 << 2)    // Repeat Start (1=Generate repeated START)

// I2SR Status Register bits
#define REG_SR_ICF      (1 << 7)    // Transfer Complete (set at 9th clock falling edge)
#define REG_SR_IAAS     (1 << 6)    // Addressed As Slave
#define REG_SR_IBB      (1 << 5)    // Bus Busy (1=Busy, set by START, cleared by STOP)
#define REG_SR_IAL      (1 << 4)    // Arbitration Lost
#define REG_SR_SRW      (1 << 2)    // Slave Read/Write (1=Slave transmit)
#define REG_SR_IIF      (1 << 1)    // I2C Interrupt (set when byte transfer complete)
#define REG_SR_RXAK     (1 << 0)    // Received Acknowledge (1=No ACK received, 0=ACK received)

