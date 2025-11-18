/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

#define VIRTIO_F_INDIRECT_DESC 28
#define VIRTIO_F_EVENT_IDX 29
#define VIRTIO_F_VERSION_1 32
#define VIRTIO_F_ACCESS_PLATFORM 33
#define VIRTIO_F_RING_PACKED 34
#define VIRTIO_F_IN_ORDER 35
#define VIRTIO_F_ORDER_PLATFORM 36
#define VIRTIO_F_SR_IOV 37
#define VIRTIO_F_NOTIFICATION_DATA 38
#define VIRTIO_F_NOTIF_CONFIG_DATA 39
#define VIRTIO_F_RING_RESET 40

void virtio_print_reserved_feature_bits(uint64_t feature)
{
    if (feature & ((uint64_t)1 << VIRTIO_F_INDIRECT_DESC)) {
        sddf_dprintf("    VIRTIO_F_INDIRECT_DESC\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_EVENT_IDX)) {
        sddf_dprintf("    VIRTIO_F_EVENT_IDX\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_VERSION_1)) {
        sddf_dprintf("    VIRTIO_F_VERSION_1\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_ACCESS_PLATFORM)) {
        sddf_dprintf("    VIRTIO_F_ACCESS_PLATFORM\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_RING_PACKED)) {
        sddf_dprintf("    VIRTIO_F_RING_PACKED\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_IN_ORDER)) {
        sddf_dprintf("    VIRTIO_F_IN_ORDER\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_ORDER_PLATFORM)) {
        sddf_dprintf("    VIRTIO_F_ORDER_PLATFORM\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_SR_IOV)) {
        sddf_dprintf("    VIRTIO_F_SR_IOV\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_NOTIFICATION_DATA)) {
        sddf_dprintf("    VIRTIO_F_NOTIFICATION_DATA\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_NOTIF_CONFIG_DATA)) {
        sddf_dprintf("    VIRTIO_F_NOTIF_CONFIG_DATA\n");
    }
    if (feature & ((uint64_t)1 << VIRTIO_F_RING_RESET)) {
        sddf_dprintf("    VIRTIO_F_RING_RESET\n");
    }
}
