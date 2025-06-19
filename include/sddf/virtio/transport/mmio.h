/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/printf.h>

/* Note this is little endian */
#define VIRTIO_MMIO_MAGIC_VALUE (0x74726976)

typedef enum {
    VIRTIO_DEVICE_ID_NET = 0x1,
    VIRTIO_DEVICE_ID_BLK = 0x2,
    VIRTIO_DEVICE_ID_CONSOLE = 0x3,
    VIRTIO_DEVICE_ID_GPU = 0x10,
} virtio_mmio_device_id_t;

typedef volatile __attribute__((packed)) struct {
    uint32_t MagicValue;
    uint32_t Version;
    uint32_t DeviceID;
    uint32_t VendorID;
    uint32_t DeviceFeatures;
    uint32_t DeviceFeaturesSel;
    uint32_t _reserved0[2];
    uint32_t DriverFeatures;
    uint32_t DriverFeaturesSel;
    uint32_t _reserved1[2];
    uint32_t QueueSel;
    uint32_t QueueNumMax;
    uint32_t QueueNum;
    uint32_t _reserved2[2];
    uint32_t QueueReady;
    uint32_t _reserved3[2];
    uint32_t QueueNotify;
    uint32_t _reserved4[3];
    uint32_t InterruptStatus;
    uint32_t InterruptACK;
    uint32_t _reserved5[2];
    uint32_t Status;
    uint32_t _reserved6[3];
    uint32_t QueueDescLow;
    uint32_t QueueDescHigh;
    uint32_t _reserved7[2];
    uint32_t QueueDriverLow;
    uint32_t QueueDriverHigh;
    uint32_t _reserved8[2];
    uint32_t QueueDeviceLow;
    uint32_t QueueDeviceHigh;
    uint32_t _reserved9[21];
    uint32_t ConfigGeneration;
    uint32_t Config[0];
} virtio_mmio_regs_t;
