/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include "time.h"

#define KHZ (1000)
#define MHZ (1000 * KHZ)
#define GHZ (1000 * MHZ)

typedef uint64_t freq_t;

static inline uint64_t freq_cycles_and_hz_to_ns(uint64_t ncycles, freq_t hz)
{
    if (hz % GHZ == 0) {
        return ncycles / (hz / GHZ);
    } else if (hz % MHZ == 0) {
        return ncycles * MS_IN_S / (hz / MHZ);
    } else if (hz % KHZ == 0) {
        return ncycles * US_IN_S / (hz / KHZ);
    }

    return (ncycles * NS_IN_S) / hz;
}

static inline freq_t freq_cycles_and_ns_to_hz(uint64_t ncycles, uint64_t ns)
{
    return (ncycles * NS_IN_S) / ns;
}

static inline uint64_t freq_ns_and_hz_to_cycles(uint64_t ns, freq_t hz)
{
    return (ns * hz) / NS_IN_S;
}
