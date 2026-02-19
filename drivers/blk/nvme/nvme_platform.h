/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * Board- and topology-specific constants: PCI BDF, memory region
 * addresses/sizes, IRQ assignment, and queue configuration.
 */

/* Queue memory allocated for this driver instance. */
#define NVME_ADMIN_QUEUE_SIZE_BYTES 0x1000U
#define NVME_IO_QUEUE_SIZE_BYTES    0x1000U

/* PCI configuration (hardcoded for x86_64 QEMU). */
#define NVME_PCI_BUS  0U
#define NVME_PCI_DEV  4U
#define NVME_PCI_FUNC 0U

/* IRQ assignment (hardcoded for x86_64 QEMU). */
#define NVME_IRQ 17U

/* I/O Port capability IDs configured for PCI config-space access. */
#define NVME_PCI_CONFIG_ADDR_IOPORT_ID 1U
#define NVME_PCI_CONFIG_DATA_IOPORT_ID 2U

/* Memory region virtual addresses (must match system mappings). */
#define NVME_CONTROLLER_VADDR 0x20000000U
#define NVME_ASQ_VADDR        0x20100000U
#define NVME_ACQ_VADDR        0x20101000U
#define NVME_IO_SQ_VADDR      0x20102000U
#define NVME_IO_CQ_VADDR      0x20103000U
#define NVME_IDENTIFY_VADDR   0x20104000U
#define NVME_PRP_SLOTS_VADDR  0x20200000U

/* Memory region physical addresses (must match system mappings). */
#define NVME_ASQ_PADDR        0x5FDF0000U
#define NVME_ACQ_PADDR        0x5FDF1000U
#define NVME_IO_SQ_PADDR      0x5FDF2000U
#define NVME_IO_CQ_PADDR      0x5FDF3000U
#define NVME_IDENTIFY_PADDR   0x5FDF4000U
#define NVME_PRP_SLOTS_PADDR  0x5FE00000U

/* Memory region sizes. */
#define NVME_ASQ_REGION_SIZE        0x1000U
#define NVME_ACQ_REGION_SIZE        0x1000U
#define NVME_IO_SQ_REGION_SIZE      0x1000U
#define NVME_IO_CQ_REGION_SIZE      0x1000U
#define NVME_IDENTIFY_REGION_SIZE   0x2000U
#define NVME_PRP_SLOTS_REGION_SIZE  0x80000U

/* Identify response buffers (one page each). */
#define NVME_IDENTIFY_BUFFER_BYTES 0x1000U
#define NVME_IDENTIFY_CTRL_VADDR   (NVME_IDENTIFY_VADDR + 0x0000U)
#define NVME_IDENTIFY_CTRL_PADDR   (NVME_IDENTIFY_PADDR + 0x0000U)
#define NVME_IDENTIFY_NS_VADDR     (NVME_IDENTIFY_VADDR + NVME_IDENTIFY_BUFFER_BYTES)
#define NVME_IDENTIFY_NS_PADDR     (NVME_IDENTIFY_PADDR + NVME_IDENTIFY_BUFFER_BYTES)

/* Host page size exponent; CC.MPS encodes page size as 2^(12 + MPS). [NVMe-2.1 §3.1.4.5, Fig. 41] */
#define NVME_PAGE_SIZE_LOG2 12U
