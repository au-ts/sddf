/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>

/**
 * This benchmarking struct is used to calculate system utilisation in the echo
 * server example. Each core has an idle thread which keeps track of total core
 * cycle count (`core_ccount`), as well as it's own cycle count (`idle_ccount`).
 * The remaining cycles can then be attributed to the system.
 *
 * The idle thread achieves this by reading the core cycle count each time it is
 * scheduled. The new value is then compared to the previously recorded value
 * (`prev_ccount`) to deduce whether the idle thread has been pre-empted between
 * reads. If the difference is sufficiently small, the idle thread assumes it
 * has NOT been pre-empted, and the difference in cycle counts is added to the
 * idle thread's cycle count.
 *
 * These cycle count values are also stored in shared memory with the echo
 * server benchmarking client, who will send them to the ipbench controller upon
 * benchmark completion.
 */
struct bench {
    /* Most recent total core cycle count */
    uint64_t core_ccount;
    /* Previously recorded total core cycle count */
    uint64_t prev_ccount;
    /* Cycles attributed to the idle thread */
    uint64_t idle_ccount;
};
