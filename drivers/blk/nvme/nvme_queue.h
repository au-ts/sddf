/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include "nvme.h"

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
        _Bool phase;
    } completion;

} nvme_queue_info_t;

// y is the submission queue index
static inline void nvme_queues_init(nvme_queue_info_t *queue, uint16_t y, volatile nvme_controller_t *nvme_controller,
                                    nvme_submission_queue_entry_t *submission_queue, uint16_t submission_capacity,
                                    nvme_completion_queue_entry_t *completion_queue, uint16_t completion_capacity)
{
    uint8_t DSTRD = (nvme_controller->cap & NVME_CAP_DSTRD_MASK) >> NVME_CAP_DSTRD_SHIFT;

    /* [NVMEe-Transport-PCIe-1.1] 3.1.2.1 SQyTDBL & 3.1.2.2 CQyHDBL
       Note: "The host should not read the doorbell registers"
    */
    volatile uint32_t *submission_doorbell = (void *)nvme_controller + NVME_PCIE_DOORBELL_OFFSET(2 * y, DSTRD);
    volatile uint32_t *completion_doorbell = (void *)nvme_controller + NVME_PCIE_DOORBELL_OFFSET(2 * y + 1, DSTRD);

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

    if ((cq_head_entry->phase_tag_and_status & BIT(0)) == queue->completion.phase) {
        return -1;
    }

    *entry = *cq_head_entry;

    queue->completion.head++;
    if (queue->completion.head == queue->completion.capacity) {
        queue->completion.head = 0;
        queue->completion.phase ^= 1;
    }

    *queue->completion.doorbell = queue->completion.head;

    return 0;
}
