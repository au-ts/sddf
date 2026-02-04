/*
 * Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#pragma once

#include <stdint.h>
#include <stddef.h>
#include <sddf/util/util.h>
#include <os/sddf.h>

#include <sddf/util/printf.h>

/* This library contains a selection of libseL4bench used for sDDF benchmarking. libsel4bench can be found here:
https://github.com/seL4/seL4_libs

The definitions are specific to ARMv8 - different definitions will need to used for different architectures. */

/* seL4 tracked benchmarking events. */
#define SEL4BENCH_EVENT_CACHE_L1I_MISS              0x01
#define SEL4BENCH_EVENT_CACHE_L1D_MISS              0x03
#define SEL4BENCH_EVENT_TLB_L1I_MISS                0x02
#define SEL4BENCH_EVENT_TLB_L1D_MISS                0x05
#define SEL4BENCH_EVENT_EXECUTE_INSTRUCTION         0x08
#define SEL4BENCH_EVENT_BRANCH_MISPREDICT           0x10

#define SEL4BENCH_EVENT_CACHE_L1I_ACCESS            0x14
#define SEL4BENCH_EVENT_CACHE_L1D_WB                0x15

/* Armv8 constants. */
#define SEL4BENCH_ARMV8A_COUNTER_CCNT 31
#define SEL4BENCH_ARMV8A_PMCR_N(x)       (((x) & 0xFFFF) >> 11u)
#define SEL4BENCH_ARMV8A_PMCR_ENABLE     BIT(0)
#define SEL4BENCH_ARMV8A_PMCR_RESET_ALL  BIT(1)
#define SEL4BENCH_ARMV8A_PMCR_RESET_CCNT BIT(2)
#define SEL4BENCH_ARMV8A_PMCR_DIV64      BIT(3)

/* A counter is an index to a performance counter on a platform.
 * The max counter index is sizeof(seL4_Word). */
typedef seL4_Word counter_t;

/* A counter_bitfield is used to select multiple counters.
 * Each bit corresponds to a counter id. */
typedef seL4_Word counter_bitfield_t;

/* An event id is the hardware id of an event. */
typedef seL4_Word event_id_t;

typedef uint64_t ccnt_t;

/* Functions that need to be inlined for speed. */
#define FASTFN inline __attribute__((always_inline))

/* Functions that must not cache miss. */
#define CACHESENSFN __attribute__((noinline, aligned(64)))

/* PMU registers. */
#define PMCR        "PMCR_EL0"
#define PMCNTENCLR  "PMCNTENCLR_EL0"
#define PMCNTENSET  "PMCNTENSET_EL0" // set of enabled counters
#define PMXEVCNTR   "PMXEVCNTR_EL0"
#define PMSELR      "PMSELR_EL0"
#define PMXEVTYPER  "PMXEVTYPER_EL0"
#define PMCCNTR     "PMCCNTR_EL0"

#define PMU_WRITE(reg, v)                      \
    do {                                       \
        seL4_Word _v = v;                         \
        asm volatile("msr  " reg ", %0" :: "r" (_v)); \
    }while(0)

#define PMU_READ(reg, v) asm volatile("mrs %0, " reg :  "=r"(v))

#define SEL4BENCH_READ_CCNT(var) PMU_READ(PMCCNTR, var);

static FASTFN void sel4bench_private_write_pmcr(uint32_t val)
{
    PMU_WRITE(PMCR, val);
}

static FASTFN uint32_t sel4bench_private_read_pmcr(void)
{
    uint64_t val;
    PMU_READ(PMCR, val);
    return (uint32_t)val;
}

#define MODIFY_PMCR(op, val) sel4bench_private_write_pmcr(sel4bench_private_read_pmcr() op (val))

typedef struct event_value {
    bool multiplexed;
    bool new;
    double last_rate;
    ccnt_t prev_cycle_count;
    ccnt_t total;
} event_value_t;

typedef struct counter_data {
    uint8_t len;
    uint8_t curr_event_idx;
    event_id_t events[2];
} counter_data_t;

counter_data_t counters[6];
event_value_t event_values[8];

char *counter_names[] = {
    "L1 i-cache misses",
    "L1 d-cache misses",
    "L1 i-tlb misses",
    "L1 d-tlb misses",
    "Instructions",
    "Branch mispredictions",
    "L1 i-cache accesses",
    "L1 d-cache write backs"
};

event_id_t benchmarking_events[] = {
    SEL4BENCH_EVENT_CACHE_L1I_MISS,
    SEL4BENCH_EVENT_CACHE_L1D_MISS,
    SEL4BENCH_EVENT_TLB_L1I_MISS,
    SEL4BENCH_EVENT_TLB_L1D_MISS,
    SEL4BENCH_EVENT_EXECUTE_INSTRUCTION,
    SEL4BENCH_EVENT_BRANCH_MISPREDICT,
    SEL4BENCH_EVENT_CACHE_L1I_ACCESS,
    SEL4BENCH_EVENT_CACHE_L1D_WB
};

// Write to set of enabled counters
static FASTFN void sel4bench_private_write_cntens(uint32_t mask)
{
    PMU_WRITE(PMCNTENSET, mask);
}

// returns set of enabled counters
static FASTFN uint32_t sel4bench_private_read_cntens(void)
{
    uint64_t mask;
    PMU_READ(PMCNTENSET, mask);
    return (uint32_t)mask;
}

// Disables counters
static FASTFN void sel4bench_private_write_cntenc(uint32_t mask)
{
    PMU_WRITE(PMCNTENCLR, mask);
}

// Reads value of selected register in PMSELR
static FASTFN uint32_t sel4bench_private_read_pmcnt(void)
{
    uint64_t val;
    PMU_READ(PMXEVCNTR, val);
    return (uint32_t)val;
}

// Writes to counter register selected in PMSELR
static FASTFN void sel4bench_private_write_pmcnt(uint32_t val)
{
    PMU_WRITE(PMXEVCNTR, val);
}

// Selects counter
static FASTFN void sel4bench_private_write_pmnxsel(uint32_t val)
{
    PMU_WRITE(PMSELR, val);
}

// Configures counter to track event
static FASTFN void sel4bench_private_write_evtsel(uint32_t val)
{
    PMU_WRITE(PMXEVTYPER, val);
}

/**
 * Initialise the sel4bench library.  Nothing else is guaranteed to work, and
 * may produce strange failures, if you don't do this first.
 *
 * Starts the cycle counter, which is guaranteed to run until
 * `sel4bench_destroy()` is called.
 */
static FASTFN void sel4bench_init()
{
    // ensure all counters are in the stopped state
    sel4bench_private_write_cntenc(-1);

    // clear div 64 flag -> PMCCNTR counts every clock cycle
    MODIFY_PMCR(&, ~SEL4BENCH_ARMV8A_PMCR_DIV64);

    // reset all counters
    MODIFY_PMCR( |, SEL4BENCH_ARMV8A_PMCR_RESET_ALL | SEL4BENCH_ARMV8A_PMCR_RESET_CCNT);

    // enable counters globally.
    MODIFY_PMCR( |, SEL4BENCH_ARMV8A_PMCR_ENABLE);

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
    // select instruction count incl. PL2 by default */
    sel4bench_private_write_pmnxsel(0x1f);
    sel4bench_private_write_evtsel(BIT(27));
#endif
    // start CCNT
    sel4bench_private_write_cntens(BIT(SEL4BENCH_ARMV8A_COUNTER_CCNT));
}

/**
 * Query how many performance counters are supported on this CPU, excluding the
 * cycle counter.
 *
 * Note that the return value is of type `seL4_Word`; consequently, this library
 * supports a number of counters less than or equal to the machine word size in
 * bits.

 * @return quantity of counters on this CPU
 */
static FASTFN seL4_Word sel4bench_get_num_counters()
{
    return SEL4BENCH_ARMV8A_PMCR_N(sel4bench_private_read_pmcr());
}

/**
 * Query the value of a set of counters. Temporarily disables counters then re-enables them once reading is finished
 *
 * `values` must point to an array of a length at least equal to the highest
 * counter index to be read (to a maximum of `sel4bench_get_num_counters()`).
 * Each counter to be read will be written to its corresponding index in this
 * array.
 *
 * @param counters bitfield indicating which counter(s) in `values` to query
 * @param values   array of counters
 *
 * @return current cycle count as in `sel4bench_get_cycle_count()`
 */
static CACHESENSFN ccnt_t sel4bench_get_counters(counter_bitfield_t mask, event_value_t *values)
{
    // store current running state
    uint32_t enable_word = sel4bench_private_read_cntens();

    // stop running counters (we do this instead of stopping the ones we're interested in because it saves an instruction)
    sel4bench_private_write_cntenc(enable_word);

    unsigned int counter = 0;
    for (; mask != 0; mask >>= 1, counter++) {
        if (mask & 1) {
            sel4bench_private_write_pmnxsel(counter);

            uint8_t event_idx = counters[counter].events[counters[counter].curr_event_idx];

            if (!values[event_idx].multiplexed) {
                values[event_idx].total = sel4bench_private_read_pmcnt();
            } else {
                uint64_t value = sel4bench_private_read_pmcnt();
                ccnt_t ccnt;
                SEL4BENCH_READ_CCNT(ccnt);

                // only start TAM once events start to occur
                if (values[event_idx].new && value == 0) continue;

                if (values[event_idx].new) {
                    values[event_idx].new = 0;    
                    values[event_idx].prev_cycle_count = ccnt;
                    values[event_idx].last_rate = (double)value / (double)ccnt;
                } else {
                    uint64_t tmp = values[event_idx].prev_cycle_count;

                    double delta_ccnt = (ccnt - values[event_idx].prev_cycle_count);
                    double new_rate = (double)value / delta_ccnt;

                    double count_interval = ((new_rate + values[event_idx].last_rate) * delta_ccnt) / 2;
                    values[event_idx].total += (uint64_t)count_interval;

                    values[event_idx].last_rate = new_rate;
                    values[event_idx].prev_cycle_count = ccnt;

                    // sddf_printf("counter %d event 0x%x value %lld ccnt %lld prev ccnt %lld newrate %lf this interval %lld\n", 
                    //     counter, benchmarking_events[event_idx], value, ccnt, tmp, new_rate, count_interval);
                }
            }
        }
    }

    ccnt_t ccnt;
    SEL4BENCH_READ_CCNT(ccnt);

    sel4bench_private_write_cntens(enable_word);

    return ccnt;
}

/**
 * Assign a counter to track a specific event.  Events are processor-specific,
 * though some common ones might be exposed through preprocessor constants.
 *
 * @param counter counter to configure
 * @param event   event to track
 */
static FASTFN void sel4bench_set_count_event(counter_t counter, event_id_t event)
{
    // select counter
    sel4bench_private_write_pmnxsel(counter);
    // reset it
    sel4bench_private_write_pmcnt(0);
    // change the event
    return sel4bench_private_write_evtsel(event);
}

/**
 * Start counting events on a set of performance counters.
 *
 * @param counters bitfield indicating which counter(s) to start
 */
static FASTFN void sel4bench_start_counters(counter_bitfield_t mask)
{
    return sel4bench_private_write_cntens(mask);
}

/**
 * Stop counting events on a set of performance counters.
 *
 * Note: Some processors may not support this operation.
 *
 * @param counters bitfield indicating which counter(s) to stop
 */
static FASTFN void sel4bench_stop_counters(counter_bitfield_t mask)
{
    return sel4bench_private_write_cntenc(mask & ~BIT(SEL4BENCH_ARMV8A_COUNTER_CCNT));
}

/**
 * Reset all performance counters to zero.  Note that the cycle counter is not a
 * performance counter, and is not reset.
 *
 */
static FASTFN void sel4bench_reset_counters(void)
{
    MODIFY_PMCR( |, SEL4BENCH_ARMV8A_PMCR_RESET_ALL);
}

/**
 * Changes the event being monitored in a counter for multiplexing.
 * Does nothing if counter only has one event assigned to it.
 *
 */
static FASTFN void sel4bench_rotate_events(void) {
    counter_bitfield_t multiplex_bf = 0;
    for (seL4_Word counter = 0; counter < sel4bench_get_num_counters(); counter++) {
        if (counters[counter].len < 2) continue;
        multiplex_bf |= BIT(counter);
    }

    if (multiplex_bf == 0) return;

    sel4bench_get_counters(multiplex_bf, event_values);

    for (seL4_Word i = 0; multiplex_bf != 0; multiplex_bf >>= 1, i++) {
        if (multiplex_bf & 1) {
            if (counters[i].curr_event_idx == counters[i].len - 1) {
                counters[i].curr_event_idx = 0;
            } else {
                counters[i].curr_event_idx++;
            }

            event_id_t event = benchmarking_events[counters[i].events[counters[i].curr_event_idx]];
            sel4bench_set_count_event(i, event);
            // sddf_printf("Change event on countr %d to 0x%x\n", i, benchmarking_events[counters[i].events[counters[i].curr_event_idx]]);
        }   
    }
}
