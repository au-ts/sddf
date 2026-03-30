/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/timer/timer_driver.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/config.h>
#include <sddf/util/util.h>
#include <sddf/util/div64.h>

extern timer_driver_config_t config;

/**
 *  Update the current time page shared with the virt. We should do this:
 *  a. whenever a timeout is complete,
 *  b. whenever the virt interacts with us.
 */
void set_shared_time_page(uint64_t curr_time)
{
    uint64_t *time_page = (uint64_t *)config.time_page.vaddr;
    *time_page = curr_time;
}

// This file implements virt-driver interaction for timer drivers.
microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_TIMER_DRIVER("Notified by %u\n", ch);
    uint64_t time = get_current_time();
    if (ch != config.virt_id) {
        LOG_TIMER_DRIVER_ERR("Protected called from channel %u ... not virt (%u)!\n",
                             ch, config.virt_id);
        return microkit_msginfo_new(0, 0);
    }
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        microkit_mr_set(0, time);
        return microkit_msginfo_new(0, 1);
    }
    case SDDF_TIMER_REQ_TIMEOUT: {
        uint64_t target = microkit_mr_get(0);
        bool success = set_new_timeout(target);
        LOG_TIMER_DRIVER("Next timeout: %zu ns\n", target);
        microkit_mr_set(0, (uint64_t)success);
        return microkit_msginfo_new(0, 1);
        break;
    }
    default:
        LOG_TIMER_DRIVER_ERR("bad request %lu to timer from channel %u\n",
                     microkit_msginfo_get_label(msginfo), ch);
        break;
    }

    // Always update time page when virt interacts with us.
    set_shared_time_page(time);

    return microkit_msginfo_new(0, 0);
}
