/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>

/* Data structure specific to VirtIO devices using PCI transport. */

typedef volatile struct __attribute__((packed)) virtio_pci_common_cfg {
    /* About the whole device. */
    uint32_t device_feature_select; /* read-write */
    uint32_t device_feature;        /* read-only for driver */
    uint32_t driver_feature_select; /* read-write */
    uint32_t driver_feature;        /* read-write */
    uint16_t config_msix_vector;    /* read-write */
    uint16_t num_queues;            /* read-only for driver */
    uint8_t device_status;          /* read-write */
    uint8_t config_generation;      /* read-only for driver */

    /* About a specific virtqueue. */
    uint16_t queue_select;      /* read-write */
    uint16_t queue_size;        /* read-write */
    uint16_t queue_msix_vector; /* read-write */
    uint16_t queue_enable;      /* read-write */
    uint16_t queue_notify_off;  /* read-only for driver */
    uint64_t queue_desc;        /* read-write */
    uint64_t queue_driver;      /* read-write */
    uint64_t queue_device;      /* read-write */
    uint16_t queue_notify_data; /* read-only for driver */
    uint16_t queue_reset;       /* read-write */
} virtio_pci_common_cfg_t;

/* Possible values for cfg_type */
/* Common configuration */
#define VIRTIO_PCI_CAP_COMMON_CFG 1
/* Notifications */
#define VIRTIO_PCI_CAP_NOTIFY_CFG 2
/* ISR Status */
#define VIRTIO_PCI_CAP_ISR_CFG 3
/* Device specific configuration */
#define VIRTIO_PCI_CAP_DEVICE_CFG 4
/* PCI configuration access */
#define VIRTIO_PCI_CAP_PCI_CFG 5
/* Shared memory region */
#define VIRTIO_PCI_CAP_SHARED_MEMORY_CFG 8
/* Vendor-specific data */
#define VIRTIO_PCI_CAP_VENDOR_CFG 9

#define PCI_CAP_ID_VNDR   0x09

typedef volatile struct __attribute__((packed)) virtio_pci_cap {
    uint8_t cap_vndr;   /* Generic PCI field: PCI_CAP_ID_VNDR */
    uint8_t cap_next;   /* Generic PCI field: next ptr. */
    uint8_t cap_len;    /* Generic PCI field: capability length */
    uint8_t cfg_type;   /* Identifies the structure. */
    uint8_t bar;        /* Where to find it. */
    uint8_t id;         /* Multiple capabilities of the same type */
    uint8_t padding[2]; /* Pad to full dword. */
    uint32_t offset;    /* Offset within bar. */
    uint32_t length;    /* Length of the structure, in bytes. */
} virtio_pci_cap_t;

typedef volatile struct __attribute__((packed)) virtio_pci_cap64 {
    virtio_pci_cap_t cap;
    uint32_t offset_hi;
    uint32_t length_hi;
};