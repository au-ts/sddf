/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <microkit.h>
#include <sddf/network/queue.h>
#include <sddf/util/string.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <ethernet_config.h>

#define VIRT_RX_CH 0
#define CLIENT_CH 1

uintptr_t invocation_counter_vaddr;
uint64_t *invocation_counter;

void notified(microkit_channel ch)
{
    if (invocation_counter_vaddr) {
        (*invocation_counter)++;
    }

    /* This copier only passes notification between VIRT_RX and CLIENT */
    switch (ch) {
    case CLIENT_CH:
        microkit_notify(VIRT_RX_CH);
        break;
    case VIRT_RX_CH:
        microkit_notify(CLIENT_CH);
        break;
    default:
        break;
    }
}

void init(void)
{
    invocation_counter = (uint64_t *)invocation_counter_vaddr;

    // Do nothing
}
