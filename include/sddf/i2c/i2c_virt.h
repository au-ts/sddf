/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stddef.h>
#include <sddf/i2c/config.h>
#include <sddf/i2c/queue.h>
#include <sddf/i2c/client.h>

#define BUS_UNCLAIMED (-1)
#define CLIENT_CH_OFFSET 1      // Channel 0 == driver. Others are clients.

#pragma once

// Virt queue. Contains a list of pending work which was deferred due to an overly full driver queue.
// We always need to clear all work in this queue before we can accept new notifications.
typedef struct virt_q_entry {
    uint32_t client_id;
    size_t num_cmds;    // We only parse as many buffers as were left behind and not more.
                        // Further cmds correspond to a new signal.
    i2c_cmd_t head_cmd; // Header command of halted request. We keep this here instead of re-inserting.
} virt_q_entry_t;

typedef struct virt_q {
    size_t head, tail;
    virt_q_entry_t list[SDDF_I2C_MAX_CLIENTS];
    // This bitmask is for sanity checking. If a single client has two deferred
    // ops something has gone terrible wrong and the virt should crash.
    uint64_t occupant_bitmask[1 + (SDDF_I2C_MAX_CLIENTS / 64)];
} virt_q_t;

/**
 * Check if a client is safe to add to the deferred work queue.
 * Returns client number on success, returns negative if invalid.
 */
static int virt_q_client_valid(virt_q_t *q, uint32_t client_id)
{
    uint8_t client_no = ((uint8_t)client_id);
    size_t byte = client_no / 64;
    uint8_t bit = client_no % 64;
    // Check client number is valid (not driver/too large) and not already in queue.
    if (client_no > SDDF_I2C_MAX_CLIENTS || q->occupant_bitmask[byte] & (1 << bit)) {
        return -1;
    }
    return client_no;
}

static inline int virt_q_empty(virt_q_t *queue)
{
    return (queue->tail - queue->head == 0);
}

int virt_q_append(virt_q_t *queue, uint32_t client_id, size_t num_cmds, i2c_cmd_t head_cmd)
{
    uint8_t client_no = virt_q_client_valid(queue, client_id);
    // Queue is full or client is invalid
    if (client_no < 0 || queue->tail - queue->head + 1 == SDDF_I2C_MAX_CLIENTS) {
        return -1;
    }
    size_t idx = queue->tail % SDDF_I2C_MAX_CLIENTS;
    queue->list[idx].client_id = client_id;
    queue->list[idx].num_cmds = num_cmds;
    queue->list[idx].head_cmd = head_cmd;
    queue->tail++;
    queue->occupant_bitmask[client_no / 64] |= (1 << (client_no % 64));
    return 0;
}

int virt_q_pop(virt_q_t *queue, uint32_t *client_id, size_t *num_cmds, i2c_cmd_t *head_cmd)
{
    // Queue is empty
    if (virt_q_empty(queue)) {
        return -1;
    }
    size_t idx = queue->head % SDDF_I2C_MAX_CLIENTS;
    *client_id = queue->list[idx].client_id;
    *num_cmds = queue->list[idx].num_cmds;
    *head_cmd = queue->list[idx].head_cmd;

    // Clear bit
    uint8_t client_no = ((uint8_t)(queue->list[idx].client_id & (uint32_t)0xff));
    assert(queue->occupant_bitmask[client_no / 64] & (1 << (client_no % 64)));
    queue->occupant_bitmask[client_no / 64] ^= (1 << (client_no % 64));
    queue->head++;
    return 0;
}

int virt_q_peek(virt_q_t *queue, uint32_t *client_id, size_t *num_cmds, i2c_cmd_t *head_cmd)
{
    // Queue is empty
    if (virt_q_empty(queue)) {
        return -1;
    }
    size_t idx = queue->head % SDDF_I2C_MAX_CLIENTS;
    *client_id = queue->list[idx].client_id;
    *num_cmds = queue->list[idx].num_cmds;
    *head_cmd = queue->list[idx].head_cmd;
    return 0;
}
