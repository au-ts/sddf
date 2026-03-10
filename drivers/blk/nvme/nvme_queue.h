/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include "nvme.h"

#include <sddf/util/fence.h>

/*
 * DW3 layout is STATUS[31:17], P[16], CID[15:0]; DW3[31:16] is stored in
 * phase_tag_and_status, so P maps to bit 0 and STATUS maps to bits 15:01.
 * [NVMe-2.1 §4.2.1, Fig. 98; §4.2.3, Fig. 100]
 */
#define NVME_CQE_PHASE_MASK BIT(0)

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

static inline void nvme_queues_init(nvme_queue_info_t *queue, uint16_t queue_id,
                                    volatile nvme_controller_t *nvme_controller,
                                    nvme_submission_queue_entry_t *submission_queue, uint16_t submission_capacity,
                                    nvme_completion_queue_entry_t *completion_queue, uint16_t completion_capacity)
{
    uint8_t doorbell_stride = (nvme_controller->cap & NVME_CAP_DSTRD_MASK) >> NVME_CAP_DSTRD_SHIFT;

    /* [NVMEe-Transport-PCIe-1.1] 3.1.2.1 SQyTDBL & 3.1.2.2 CQyHDBL
       Note: "The host should not read the doorbell registers"
    */
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
    //TODO: consider mapping the queue regions cached and add appropriate cache maintenance operations here
    queue->submission.queue[queue->submission.tail] = *entry;

    THREAD_MEMORY_RELEASE();

    queue->submission.tail++;
    if (queue->submission.tail == queue->submission.capacity) {
        queue->submission.tail = 0;
    }

    *queue->submission.doorbell = queue->submission.tail;
}

static inline int nvme_queue_consume(nvme_queue_info_t *queue, nvme_completion_queue_entry_t *entry)
{
    //TODO: consider mapping the queue regions cached and add appropriate cache maintenance operations here
    nvme_completion_queue_entry_t *cq_head_entry = &queue->completion.queue[queue->completion.head];

    if ((cq_head_entry->phase_tag_and_status & NVME_CQE_PHASE_MASK) == queue->completion.phase) {
        return -1;
    }

    THREAD_MEMORY_ACQUIRE();

    *entry = *cq_head_entry;

    queue->completion.head++;
    if (queue->completion.head == queue->completion.capacity) {
        queue->completion.head = 0;
        queue->completion.phase ^= 1;
    }

    *queue->completion.doorbell = queue->completion.head;

    return 0;
}
