/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * PCI Configuration helpers for BAR and interrupt discovery (Mechanism #1).
 */

#include <stdint.h>

#include <microkit.h>
#include <sddf/util/util.h>
#include "nvme_bits.h"

/* PCI Configuration Mechanism #1 I/O ports. [PCI-3.0 §3.2.2.3.2] */
#define NVME_PCIE_CFG_ADDR_PORT 0xCF8U
#define NVME_PCIE_CFG_DATA_PORT 0xCFCU

/* PCI config address encoding. [PCI-3.0 §3.2.2.3.2] */
#define NVME_PCIE_CFG_ADDR_ENABLE      BIT(31)
#define NVME_PCIE_CFG_ADDR_BUS_SHIFT   16U
#define NVME_PCIE_CFG_ADDR_DEV_SHIFT   11U
#define NVME_PCIE_CFG_ADDR_FUNC_SHIFT  8U
#define NVME_PCIE_CFG_ADDR_OFFSET_MASK 0xFCU

/* Type 0/1 configuration space register offsets. [NVMe-PCIe-1.1 §3.8.1, Fig. 10] */
#define NVME_PCIE_CFG_OFFSET_ID          0x00U
#define NVME_PCIE_CFG_OFFSET_COMMAND     0x04U
#define NVME_PCIE_CFG_OFFSET_BAR0        0x10U
#define NVME_PCIE_CFG_OFFSET_INTR_INFO   0x3CU

/* Command register bits. [PCI-3.0 §6.2.2, Table 6-1] */
#define NVME_PCIE_COMMAND_MEMORY_SPACE_ENABLE BIT(1)
#define NVME_PCIE_COMMAND_BUS_MASTER_ENABLE   BIT(2)

/* Interrupt information field layout. [PCIe2-0.9 §7.5.1.20] */
#define NVME_PCIE_INTR_LINE_MASK  NVME_BITS_MASK(0, 7)
#define NVME_PCIE_INTR_PIN_SHIFT  8U
#define NVME_PCIE_INTR_PIN_MASK   NVME_BITS_MASK(8, 15)

static inline uint32_t nvme_pcie_cfg_address(uint8_t bus, uint8_t dev, uint8_t func, uint8_t offset)
{
    return NVME_PCIE_CFG_ADDR_ENABLE | ((uint32_t)bus << NVME_PCIE_CFG_ADDR_BUS_SHIFT)
         | ((uint32_t)dev << NVME_PCIE_CFG_ADDR_DEV_SHIFT) | ((uint32_t)func << NVME_PCIE_CFG_ADDR_FUNC_SHIFT)
         | ((uint32_t)offset & NVME_PCIE_CFG_ADDR_OFFSET_MASK);
}

/* Access PCI config space using Mechanism #1 I/O ports. [PCI-3.0 §3.2.2.3.2] */
static inline uint32_t pci_config_read_32(uint8_t addr_ioport_id, uint8_t data_ioport_id, uint8_t bus, uint8_t dev,
                                          uint8_t func, uint8_t offset)
{
    uint32_t address = nvme_pcie_cfg_address(bus, dev, func, offset);
    microkit_x86_ioport_write_32(addr_ioport_id, NVME_PCIE_CFG_ADDR_PORT, address);
    return microkit_x86_ioport_read_32(data_ioport_id, NVME_PCIE_CFG_DATA_PORT);
}

/* Write one 32-bit value to PCI config space using Mechanism #1 I/O ports. */
static inline void pci_config_write_32(uint8_t addr_ioport_id, uint8_t data_ioport_id, uint8_t bus, uint8_t dev,
                                       uint8_t func, uint8_t offset, uint32_t value)
{
    uint32_t address = nvme_pcie_cfg_address(bus, dev, func, offset);
    microkit_x86_ioport_write_32(addr_ioport_id, NVME_PCIE_CFG_ADDR_PORT, address);
    microkit_x86_ioport_write_32(data_ioport_id, NVME_PCIE_CFG_DATA_PORT, value);
}
