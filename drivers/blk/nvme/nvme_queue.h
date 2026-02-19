/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

/*
 * Host-side NVMe queue tracking: SQ/CQ state, doorbell writes,
 * ring-buffer submit/consume helpers, and phase-bit management.
 */

#include <stdbool.h>
#include <stdint.h>
#include "nvme_regs.h"
#include "nvme_cmd.h"

/*
 * Host-side queue tracking state for one SQ/CQ pair.
 */
typedef struct nvme_queue_info {
    struct {
        nvme_submission_queue_entry_t *queue;
        uint16_t capacity;
        uint16_t tail;
        volatile uint32_t *doorbell;
    } submission;

    struct {
        nvme_completion_queue_entry_t *queue;
        uint16_t capacity;
        uint16_t head;
        volatile uint32_t *doorbell;
        bool phase;
    } completion;

} nvme_queue_info_t;

static inline void nvme_queues_init(nvme_queue_info_t *queue, uint16_t queue_id,
                                    volatile nvme_controller_t *nvme_controller,
                                    nvme_submission_queue_entry_t *submission_queue, uint16_t submission_capacity,
                                    nvme_completion_queue_entry_t *completion_queue, uint16_t completion_capacity)
{
    uint8_t doorbell_stride = (nvme_controller->cap & NVME_CAP_DSTRD_MASK) >> NVME_CAP_DSTRD_SHIFT;

    /* Host should write, not read, SQ/CQ doorbells. [NVMe-PCIe-1.1 §3.1.2.1, §3.1.2.2] */
    volatile uint32_t *submission_doorbell = (void *)nvme_controller
                                           + NVME_PCIE_SQTDBL_OFFSET(queue_id, doorbell_stride);
    volatile uint32_t *completion_doorbell = (void *)nvme_controller
                                           + NVME_PCIE_CQHDBL_OFFSET(queue_id, doorbell_stride);

    *queue = (nvme_queue_info_t){
        .submission = {
            .queue = submission_queue,
            .capacity = submission_capacity,
            .tail = 0,
            .doorbell = submission_doorbell,
        },
        .completion = {
            .queue = completion_queue,
            .capacity = completion_capacity,
            .head = 0,
            .doorbell = completion_doorbell,
            /* Initial phase is 0 before controller ownership. [NVMe-2.1 §4.2.4, Fig. 98, Fig. 108] */
            .phase = 0,
        },
    };
}

static inline void nvme_queue_submit(nvme_queue_info_t *queue, nvme_submission_queue_entry_t *entry)
{
    queue->submission.queue[queue->submission.tail] = *entry;

    queue->submission.tail++;
    if (queue->submission.tail == queue->submission.capacity) {
        queue->submission.tail = 0;
    }

    *queue->submission.doorbell = queue->submission.tail;
}

static inline int nvme_queue_consume(nvme_queue_info_t *queue, nvme_completion_queue_entry_t *entry)
{
    nvme_completion_queue_entry_t *cq_head_entry = &queue->completion.queue[queue->completion.head];

    /* Completion ownership is tracked by phase bit. [NVMe-2.1 §4.2.4] */
    if ((cq_head_entry->phase_tag_and_status & NVME_CQE_PHASE_MASK) == queue->completion.phase) {
        return -1;
    }

    *entry = *cq_head_entry;

    queue->completion.head++;
    if (queue->completion.head == queue->completion.capacity) {
        queue->completion.head = 0;
        queue->completion.phase ^= 1;
    }

    /* Advancing CQ head is committed by writing CQyHDBL. [NVMe-2.1 §3.3.1.2; NVMe-PCIe-1.1 §3.1.2.2] */
    *queue->completion.doorbell = queue->completion.head;

    return 0;
}
