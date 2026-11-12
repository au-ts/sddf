/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <os/sddf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/config.h>
#include <stdint.h>
#ifdef MULTIKERNEL
#include <sddf/util/multikernel.h>
#endif

const sddf_timer_virt_config_t *timer_config;

typedef struct timeout {
    struct timeout *next;
    struct timeout *prev;
    uint64_t timestamp;
    sddf_channel identity;
} timeout_t;

typedef struct {
    timeout_t entries[SDDF_TIMER_MAX_CLIENTS];
    timeout_t *head;
} timeouts_t;

static timeouts_t timeouts;

static void remove_timeout(timeout_t *timeout)
{
    if (timeout->prev) {
        timeout->prev->next = timeout->next;
    } else if (timeouts.head == timeout) {
        timeouts.head = timeout->next;
    }

    if (timeout->next) {
        timeout->next->prev = timeout->prev;
    }
    timeout->next = timeout->prev = NULL;
}

static void set_timeout(sddf_channel ch, uint64_t timestamp)
{
    timeout_t *timeout = &timeouts.entries[ch];
    remove_timeout(timeout);
    timeout->timestamp = timestamp;
    timeout_t *next = timeouts.head;
    timeout_t *prev = NULL;
    while (next && next->timestamp <= timestamp) {
        prev = next;
        next = next->next;
    }
    timeout->prev = prev;
    timeout->next = next;
    if (prev) {
        prev->next = timeout;
    } else {
        timeouts.head = timeout;
    }
    if (next) {
        next->prev = timeout;
    }
}

static void schedule(void)
{
    uint64_t now = sddf_read_counter();
    while (timeouts.head && timeouts.head->timestamp <= now) {
        timeout_t *expired = timeouts.head;
        remove_timeout(expired);
        sddf_notify(expired->identity);
        now = sddf_read_counter();
    }
    if (timeouts.head) {
        sddf_set_mr(0, timeouts.head->timestamp);
        sddf_ppcall(timer_config->driver_id, seL4_MessageInfo_new(SDDF_TIMER_SET_TIMEOUT, 0, 0, 1));
    }
}

static void consume_request(sddf_channel ch)
{
    uint64_t *slot = (uint64_t *)timer_config->req_vaddrs[ch];
    uint64_t deadline = __atomic_exchange_n(slot, UINT64_MAX, __ATOMIC_ACQUIRE);
    if (deadline != UINT64_MAX) {
        set_timeout(ch, deadline);
    }
}

void init(void)
{
    assert(timer_config_check_magic(timer_config));
    for (sddf_channel ch = 0; ch < SDDF_TIMER_MAX_CLIENTS; ch++) {
        timeouts.entries[ch].identity = ch;
    }
}

void notified(sddf_channel ch)
{
#ifdef MULTIKERNEL
    sddf_multikernel_ack(ch);
#endif
    if (ch != timer_config->driver_id) {
        if (ch >= SDDF_TIMER_MAX_CLIENTS || !timer_config->req_vaddrs[ch]) {
            return;
        }
        consume_request(ch);
    }
    schedule();
}
