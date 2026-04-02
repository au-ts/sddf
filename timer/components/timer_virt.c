/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <microkit.h>
#include <stdint.h>
#include <sddf/timer/protocol.h>
#include <sddf/timer/timer_virt.h>
#include <sddf/util/util.h>

__attribute__((__section__(".timer_virt_config"))) timer_virt_config_t config;

// Priority heap for managing timeouts
static timer_heap_t timeouts;
static uint64_t last_issued_timeout = 0;

static void process_timeouts(void)
{
    uint64_t curr_time = read_timeout_stamp_page((uint64_t *)config.time_page.vaddr);
    LOG_TIMER_VIRT("Processing timeouts.\n");

    // Pop from priority heap until all timeouts are serviced
    while (timer_heap_peek(&timeouts) != NULL && timer_heap_peek(&timeouts)->timestamp <= curr_time) {
        // Refresh current time each loop, in case we are pre-empted by driver.
        curr_time = read_timeout_stamp_page((uint64_t *)config.time_page.vaddr);
        LOG_TIMER_VIRT("Last timeout: %zu ns\n", curr_time);
        timeout_t expired;
        assert(timer_heap_pop(&timeouts, &expired));
        // If the expired timeout is periodic, re-enqueue it.
        if (expired.period != 0) {
            // NOTE: this func updates the timestamp based on the period.
            // If this assert fails, the heap is broken. We should always be able
            // to reinsert if we just popped.
            if (expired.timestamp < curr_time - expired.period) {
                // If the timestamp was further in the past than one period, we should
                // adjust the timestamp to skip any repeated periods that would happen at the
                // same moment. This is necessary to prevent triggering potentially hundreds
                // of thousands of timeouts with a single PPC, at the same time!
                uint64_t timestamp_period_delta = curr_time - expired.timestamp;
                uint64_t old_timestamp = expired.timestamp;
                expired.timestamp += expired.period * ((timestamp_period_delta / expired.period));
                LOG_TIMER_VIRT_ERR("Periodic timeout requested with past time. Skipping %zu -> %zu\n",
                                   old_timestamp, expired.timestamp);
            }
            LOG_TIMER_VIRT("Re-inserting periodic timeout with period=%zu\n", expired.period);
            assert(timer_heap_reinsert_periodic(&timeouts, &expired));
        } else {
            // Free the ID of this timeout if we're discarding it

            free_timeout_id(&timeouts, expired.id);
        }
        LOG_TIMER_VIRT("timeout #%zu @ %zu ns expired for client %u\n", expired.id, expired.timestamp, expired.client_channel);
        microkit_notify(expired.client_channel);
    }

    timeout_t *next = timer_heap_peek(&timeouts);
    // Reissue next timeout irq, if needed.
    if (next != NULL) {
        if (next->timestamp != last_issued_timeout) {
            uint64_t next_timeout = next->timestamp;
            LOG_TIMER_VIRT("next delay: %zu\n", next_timeout);
            // Load next timeout into driver
            timer_virt_set_timeout(config.driver_id, next_timeout);
            last_issued_timeout = next_timeout;
        } else {
            LOG_TIMER_VIRT("Next timeout already issued. Not re-issuing.\n");
        }
    } else {
        LOG_TIMER_VIRT("No more timeouts remain. Idling.\n");
    }
}

void notified(microkit_channel ch)
{
    if (ch == config.driver_id) {
        LOG_TIMER_VIRT("notified by driver\n");
        process_timeouts();
    } else {
        LOG_TIMER_VIRT("Invalid notification from channel %u!\n", ch);
    }
}


microkit_msginfo protected(microkit_channel ch, microkit_msginfo msginfo)
{
    LOG_TIMER_VIRT("ppc from channel %u\n", ch);
    microkit_msginfo ret;
    switch (microkit_msginfo_get_label(msginfo)) {
    case SDDF_TIMER_GET_TIME: {
        seL4_SetMR(0, timer_virt_get_time(config.driver_id));
        return microkit_msginfo_new(SDDF_TIMER_ERR_OK, 1);
    }
    case SDDF_TIMER_REQ_TIMEOUT: {
        uint64_t target_time = seL4_GetMR(SDDF_TIMER_REQ_TIMEOUT_TIMEOUT);
        uint64_t period = seL4_GetMR(SDDF_TIMER_REQ_TIMEOUT_PERIOD);
        uint64_t id;
        LOG_TIMER_VIRT("setting timeout for %zuns\n", target_time);
        // Check period is sane
        if (period <= SDDF_TIMER_MIN_PERIOD_NS) {
            LOG_TIMER_VIRT_ERR("Tried to set a periodic timeout with invalid period %zu!\n", period);
            ret = microkit_msginfo_new(SDDF_TIMER_ERR_EINVAL, 0);
            break;
        }
        bool success = timer_heap_insert(&timeouts, target_time, period, ch, &id);
        if (success) {
            process_timeouts();
            microkit_mr_set(0, id); // return timeout id
            ret = microkit_msginfo_new(SDDF_TIMER_ERR_OK, 1);
        } else {
            // Heap is full!
            ret = microkit_msginfo_new(SDDF_TIMER_ERR_UNAVAILABLE, 0);
        }
        break;
    }
    case SDDF_TIMER_CANCEL_TIMEOUT: {
        uint64_t target_id = microkit_mr_get(SDDF_TIMER_CANCEL_TIMEOUT_ID);
        bool success = timer_heap_delete(&timeouts, target_id, ch);
        if (!success) {
            LOG_TIMER_VIRT_ERR("Failed to delete timeout with ID=%zu for client %u!\n",
                               target_id, ch);
            LOG_TIMER_VIRT_ERR("Ensure timeout ID and requesting client is correct.\n");
            ret = microkit_msginfo_new(SDDF_TIMER_ERR_EINVAL, 0);
        } else {
            ret = microkit_msginfo_new(SDDF_TIMER_ERR_OK, 0);
        }
        break;
    }
    default:
        LOG_TIMER_VIRT("Unknown request %lu to timer from channel %u\n", microkit_msginfo_get_label(msginfo), ch);
        ret = microkit_msginfo_new(SDDF_TIMER_ERR_PPC, 0);
        break;
    }

    return ret;
}


void init(void)
{
    // Initialise priority heap
    timer_heap_init(&timeouts);
    LOG_TIMER_VIRT("Driver id: %u\n", config.driver_id);
}
