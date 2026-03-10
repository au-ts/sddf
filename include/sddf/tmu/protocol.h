/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdint.h>
#include <stdbool.h>

// PPC interface for interacting with TMU driver
// NOTE: this driver class currently only supports a SINGLE temperature source,
// ideally measuring the CPU or SoC temp.

typedef double sddf_temp_celsius_t;
typedef enum {
    SDDF_TMU_SET_ENABLED,
    SDDF_TMU_SET_IRQ_MODE,
    SDDF_TMU_SET_IRQ_THRESHOLD,
    SDDF_TMU_GET_TEMP
} sddf_tmu_ppc_codes_t;

typedef enum {
    SDDF_TMU_IRQ_MODE_DISABLED,
    SDDF_TMU_IRQ_MODE_INSTANTANEOUS,    // IRQ on instant of threshold exceeding
    SDDF_TMU_IRQ_MODE_AVG   // IRQ when low-passed average exceeds theshold
} sddf_tmu_irq_modes_t;

typedef enum {
    SDDF_TMU_ERR_OK,
    SDDF_TMU_ERR_UNPERMITTED,
    SDDF_TMU_ERR_FAILED,
    SDDF_TMU_ERR_EINVAL,
    SDDF_TMU_NUM_ERRORS
} sddf_tmu_err_t;

typedef struct tmu_temp_info {
    sddf_temp_celsius_t temp_inst;
    sddf_temp_celsius_t temp_avg;
    bool valid; // Temp was outside of safe boundaries
} sddf_tmu_temp_info_t;

// SDDF_TMU_SET_ENABLED
// Enable or disable the TMU.
// Args:
// MR0: 0 to disable, 1 to enable
// Returns:
// MR0: 0 on success, 1 on failure.
#define SDDF_TMU_SET_ENABLED_ENABLE (0)
#define SDDF_TMU_SET_ENABLED_SUCCESS (0)
#define SDDF_TMU_SET_ENABLED_FAIL (1)

// SDDF_TMU_SET_IRQ_MODE
// Set the IRQ forwarding to disabled or active with a direct or low-pass average theshold. Forwarded interrupts are sent to
// Args:
// MR0: mode. 0 = disabled, 1 = instantaneous, 2 = average
// Returns:
// MR0: 0 on success, 1 on failure.
#define SDDF_TMU_SET_IRQ_MODE_MODE (0)
#define SDDF_TMU_SET_IRQ_MODE_SUCCESS (0)
#define SDDF_TMU_SET_IRQ_MODE_FAIL (1)

// SDDF_TMU_SET_IRQ_THESHOLD
// Set the bounds for IRQ delivery
// Args:
// MR0: high theshold in degrees celsius
// Returns:
// MR0: 0 on success, 1 on failure.
#define SDDF_TMU_SET_IRQ_THRESHOLD_THRESHOLD (0)
#define SDDF_TMU_SET_IRQ_THRESHOLD_SUCCESS (0)
#define SDDF_TMU_SET_IRQ_THRESHOLD_FAIL (1)

// SDDF_TMU_GET_TEMP
// Return temperature reading.
// Args: (none)
// Returns:
// MR0: 0 on success, 1 on failure.
// MR1: reading value. 0 if invalid, 1 if valid
// MR2: instantaneous temperature in celsius
// MR3: average temperature in celsius
#define SDDF_TMU_GET_TEMP_SUCCESS (0)
#define SDDF_TMU_GET_TEMP_FAIL (1)
#define SDDF_TMU_GET_TEMP_VALIDITY (1)
#define SDDF_TMU_GET_TEMP_INST (2)
#define SDDF_TMU_GET_TEMP_AVG (3)

