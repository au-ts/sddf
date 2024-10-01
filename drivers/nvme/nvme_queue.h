#pragma once

#include "nvme.h"

static inline void nvme_queue_submit(volatile nvme_submission_queue_entry_t queue[], volatile void *nvme_controller,
                                     uint16_t DSTRD, nvme_submission_queue_entry_t *entry)
{
    uint16_t sq_tail = nvme_sqytdbl_read(nvme_controller, DSTRD, 0);
    queue[sq_tail] = *entry;

    // todo: overflow?
    nvme_sqytdbl_write(nvme_controller, DSTRD, 0, ++sq_tail);
}


// TODO: per-queue.
static int phase = 0;


// 4.2.41 phase tag
#include <sddf/util/printf.h>
#include <sddf/util/fence.h>
__attribute__((noinline))
static int nvme_queue_consume(volatile nvme_completion_queue_entry_t queue[], volatile void *nvme_controller,
                                    uint16_t DSTRD, nvme_completion_queue_entry_t *entry)
{
    uint16_t cq_head = nvme_cqyhdbl_read(nvme_controller, DSTRD, 0);

    /* if the head is not new */
    if ((queue[cq_head].phase_tag_and_status & BIT(0)) == phase) {
        return -1;
    }

    *entry = queue[cq_head];

    cq_head++; /* TODO: wrapping */
    // if (cq_head == length) {
    //     cq_head = 0;
    //     phase ^= 1; /* flip phase */
    // }

    nvme_cqyhdbl_write(nvme_controller, DSTRD, 0, cq_head);
    return 0;
}
