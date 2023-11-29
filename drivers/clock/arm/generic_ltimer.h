/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include "util/printf.h"

/**
 * This file provides the interface for an OS independant consisent timer interface.
 *
 * Implementations of this interface vary per platform - for some platforms,
 * a single timer driver will back the implementation, for others, there may be many.
 */

typedef enum {
    TIMEOUT_PERIODIC,
    TIMEOUT_ABSOLUTE,
    TIMEOUT_RELATIVE
} timeout_type_t;

typedef enum {
    LTIMER_TIMEOUT_EVENT,
    LTIMER_OVERFLOW_EVENT
} ltimer_event_t;

/*
 * Type signature of the callback function that can be accepted by the ltimer.
 * The callbacks are invoked when an event occurs. These events are described
 * by the ltimer_event_t type.
 *
 * The callbacks are expected to be reentrant with regards to the ltimer state.
 * More specifically, the ltimer interface cannot guarantee that the internal
 * state will be race-safe if two different callbacks invoke the ltimer API
 * functions concurrently.
 */
typedef void (*ltimer_callback_fn_t)(void *token, ltimer_event_t event);

//@ericc: stripped down so that it doesn't multiplex
/* logical timers are the interface used by the timer manager to multiplex
 * timer requests from clients - only one timeout can be registered at a time.
 * logical timers may be backed by several timer drivers to implement the
 * functionality
 */
typedef struct ltimer {
    /*
     * Read the current time in nanoseconds. Precision depends on the implementation, but
     * the value is guaranteed to be monotonically increasing and at least millisecond accurate.
     *
     * @param data     for the logical timer to use
     * @param[out] time variable to read the time value into
     * @return          0 on success, errno on error.
     */
    int (*get_time)(void *data, uint64_t *time);

    /*
     * Set an irq to come in at a specific time.
     *
     * IRQs may come in earlier than requested due to implementation details.
     *
     * @param data     for the logical timer to use
     * @param ns       ns value (depends on timer type)
     * @param type     type of timeout
     * @return         0 on success, errno on error.
     */
    int (*set_timeout)(void *data, uint64_t ns, timeout_type_t type);

    /*
     * Reset the timer into a state similar to what it was when first initialized. This
     * should cancel any outstanding timeouts etc. It may or may not cause the monotonic
     * upcounter to change (by resetting to 0 or otherwise)
     *
     * @param data     for the logical timer to use
     * @return         0 on success, errno on error.
     */
    int (*reset)(void *data);

    /* Destroy an ltimer, freeing any resources and turning off devices */
    void (*destroy)(void *data);

    /* data for the implementation to use */
    void *data;
} ltimer_t;

/* Spinning delay functions */
static inline void ltimer_ns_delay(ltimer_t *timer, uint64_t nanoseconds) {
    uint64_t start, end;

    int error = ltimer_get_time(timer, &start);
    /* spin */
    for (int i = 0; !error; i++) {
        error = ltimer_get_time(timer, &end);
        if (end - start >= nanoseconds) {
            break;
        } else if (i % 1000 == 0 && start == end) {
            printf("Time doesn't appear to be changing\n");
        }
    }
}

static inline void ltimer_s_delay(ltimer_t *timer, uint64_t seconds) {
    ltimer_ns_delay(timer, seconds * NS_IN_S);
}

static inline void ltimer_ms_delay(ltimer_t *timer, uint64_t milliseconds) {
    ltimer_ns_delay(timer, milliseconds * NS_IN_MS);
}

static inline void ltimer_us_delay(ltimer_t *timer, uint64_t microseconds) {
    ltimer_ns_delay(timer, microseconds * NS_IN_US);
}

/*
 * default init function -> platforms may provide multiple ltimers, but each
 * must have a default
 *
 * The callback functions will be invoked every single time an event described
 * by the 'ltimer_event_t' type occurs. A reminder that care should be taken
 * with calling the ltimer functions inside the callback, the ltimer interface
 * functions are not reentrant.
 */
int ltimer_default_init(ltimer_t *timer, ltimer_callback_fn_t callback, void *callback_token);