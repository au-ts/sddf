/*
 * Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <assert.h>

#include "timer/time.h"
#include "timer/frequency.h"
#include "timer/generic_ltimer.h"
#include "arch/aarch64/generic_timer.h"

#include "util/printf.h"

typedef struct {
    uint32_t freq; // frequency of the generic timer
    uint64_t period; // period of a current periodic timeout, in ns
    irq_id_t timer_irq_id;
    timer_callback_data_t callback_data;
    ltimer_callback_fn_t user_callback;
    void *user_callback_token;
} generic_ltimer_t;

static int get_time(void *data, uint64_t *time)
{
    assert(data != NULL);
    assert(time != NULL);

    generic_ltimer_t *ltimer = data;
    uint64_t ticks = generic_timer_get_ticks();
    *time = freq_cycles_and_hz_to_ns(ticks, ltimer->freq);
    return 0;
}

int set_timeout(void *data, uint64_t ns, timeout_type_t type)
{
    generic_ltimer_t *ltimer = data;
    if (type == TIMEOUT_PERIODIC) {
        ltimer->period = ns;
    } else {
        ltimer->period = 0;
    }

    uint64_t time;
    int error = get_time(data, &time);
    if (type != TIMEOUT_ABSOLUTE) {
        if (error) {
            return error;
        }
        ns += time;
    }

    if (time > ns) {
        return ETIME;
    }
    generic_timer_set_compare(freq_ns_and_hz_to_cycles(ns, ltimer->freq));

    return 0;
}

static int handle_irq(void *data, ps_irq_t *irq)
{
    if (irq->type != PS_PER_CPU &&
        irq->cpu.number != GENERIC_TIMER_PCNT_IRQ &&
        irq->cpu.trigger != 0 &&
        irq->cpu.cpu_idx != 0) {
        return EINVAL;
    }

    generic_ltimer_t *ltimer = data;
    if (ltimer->period) {
        set_timeout(data, ltimer->period, TIMEOUT_PERIODIC);
    } else {
        generic_timer_set_compare(UINT64_MAX);
    }

    /* Interrupts are only generated for the timeout portion */
    if (ltimer->user_callback) {
        ltimer->user_callback(ltimer->user_callback_token, LTIMER_TIMEOUT_EVENT);
    }
    return 0;
}

static int reset(void *data)
{
    generic_ltimer_t *generic_ltimer = data;
    generic_ltimer->period = 0;
    generic_timer_set_compare(UINT64_MAX);
    return 0;
}

static void destroy(void *data)
{
    int error;
    generic_ltimer_t *generic_ltimer = data;
    generic_timer_disable();
}

int ltimer_default_init(ltimer_t *ltimer, ltimer_callback_fn_t callback, void *callback_data)
{
    if (ltimer == NULL) {
        printf("ltimer cannot be NULL\n");
        return EINVAL;
    }

    ltimer->get_time = get_time;
    ltimer->set_timeout = set_timeout;
    ltimer->reset = reset;
    ltimer->destroy = destroy;

    // Initialise ltimer->data with some static memory
    generic_ltimer_t *generic_ltimer;
    ltimer->data = generic_ltimer;

    generic_ltimer->user_callback = callback;
    generic_ltimer->user_callback_token = callback_data;

    generic_ltimer->freq = generic_timer_get_freq();
    if (generic_ltimer->freq == 0) {
        printf("Couldn't read timer frequency\n");
        return ENXIO;
    }

    generic_timer_set_compare(UINT64_MAX);
    generic_timer_enable();

    /* register the IRQ with sel4 */
    error = ps_calloc(&ops.malloc_ops, 1, sizeof(ps_irq_t), (void **) &generic_ltimer->callback_data.irq);
    if (error) {
        destroy(ltimer->data);
        return error;
    }
    generic_ltimer->callback_data.ltimer = ltimer;
    generic_ltimer->callback_data.irq_handler = handle_irq;
    error = get_nth_irq(ltimer->data, 0, generic_ltimer->callback_data.irq);
    if (error) {
        destroy(ltimer->data);
        return error;
    }
    generic_ltimer->timer_irq_id = ps_irq_register(&ops.irq_ops, *generic_ltimer->callback_data.irq,
                                                   handle_irq_wrapper, &generic_ltimer->callback_data);
    if (generic_ltimer->timer_irq_id < 0) {
        destroy(ltimer->data);
        return EIO;
    }

    return 0;
}