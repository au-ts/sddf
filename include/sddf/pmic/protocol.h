/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stdint.h>

// PPC interface for PMIC device class
// DANGER: current PMIC class is DUMB. It will not automatically solve constraints,
// each operation here is a best-effort direct operation on hardware.

typedef enum {
    SDDF_PMIC_ENABLE_REG = 0U,
    SDDF_PMIC_DISABLE_REG,
    SDDF_PMIC_SET_VOUT,
    SDDF_PMIC_SET_CLIMIT,
    SDDF_PMIC_GET_REG_INFO,
    SDDF_PMIC_PPC_INVALID
} sddf_pmic_ppc_codes_t;

typedef enum {
    SDDF_PMIC_ERR_OK = 0U,
    SDDF_PMIC_ERR_FAIL_REG,
    SDDF_PMIC_ERR_BAD_SETTING,
    SDDF_PMIC_ERR_NOT_IMPLEMENTED,
    SDDF_PMIC_ERR_BAD_PPC_CALL,
    SDDF_PMIC_ERR_BUSY,
    SDDF_PMIC_ERR_OTHER,
} sddf_pmic_err_t;

typedef struct {
    uint64_t enabled;
    uint64_t voltage_uv;
    uint64_t current_ua;
    uint64_t min_voltage_uv;
    uint64_t max_voltage_uv;
    uint64_t min_current_ua;
    uint64_t max_current_ua;
    uint64_t ramprate;
} sddf_pmic_reg_info_t;

// ## PPCs ##
// SDDF_PMIC_ENABLE_REG
// Enable a given regulator
// Args:
// MR0: reg_id (defined per device, in bindings file)
// Returns:
// MR0: 0 on success, nonzero on failure
#define SDDF_PMIC_ENABLE_REG_REG_ID (0)
#define SDDF_PMIC_ENABLE_REG_SUCCESS (0)
#define SDDF_PMIC_ENABLE_REG_FAIL (1)

// SDDF_PMIC_DISABLE_REG
// Disable a given regulator
// Args:
// MR0: reg_id
// Returns:
// MR0: 0 on success, nonzero on failure
#define SDDF_PMIC_DISABLE_REG_REG_ID (0)
#define SDDF_PMIC_DISABLE_REG_SUCCESS (0)
#define SDDF_PMIC_DISABLE_REG_FAIL (1)

// SDDF_PMIC_SET_VOUT
// Set the voltage output level for a regulator, if that regulator has adjustable voltage.
// Args:
// MR0: reg_id
// MR1: voltage (microvolts)
// MR2: operating mode id (defined per regulator, per device, in bindings file)
// Returns:
// MR0: 0 on success, 1 if regulator invalid, 2 if voltage setting invalid for valid reg.
// NOTE: if a regulator doesn't support voltage setting, error 1 is returned.
#define SDDF_PMIC_SET_VOUT_REG_ID (0)
#define SDDF_PMIC_SET_VOUT_VOLTAGE_UV (1)
#define SDDF_PMIC_SET_VOUT_OP_MODE_ID (2)
#define SDDF_PMIC_SET_VOUT_SUCCESS (0)
#define SDDF_PMIC_SET_VOUT_FAIL_BADREG (1)
#define SDDF_PMIC_SET_VOUT_FAIL_BADVOLTAGE (2)

// SDDF_PMIC_SET_CLIMIT
// Set the current limit of a regulator, if that regulator has a current limit setting.
// Args:
// MR0: reg_id
// MR1: current (uA)
// MR2: operating mode id (defined per regulator, per device, in bindings file)
// Returns:
// MR0: 0 on success, 1 if regulator invalid, 2 if current setting invalid for valid reg.
// NOTE: if a regulator doesn't support current setting, error 1 is returned.
#define SDDF_PMIC_SET_CLIMIT_REG_ID (0)
#define SDDF_PMIC_SET_CLIMIT_CURRENT_UA (1)
#define SDDF_PMIC_SET_CLIMIT_OP_MODE_ID (2)
#define SDDF_PMIC_SET_CLIMIT_SUCCESS (0)
#define SDDF_PMIC_SET_CLIMIT_FAIL_BADREG (1)
#define SDDF_PMIC_SET_CLIMIT_FAIL_BADCURRENT (2)

// SDDF_PMIC_GET_REG_INFO
// Get information about a regulator, including the current state as well as capabilities.
// Args:
// MR0: reg_id
// Returns:
// MR0: 0 on success, 1 if invalid.
// MR1: enabled
// MR2: current voltage (microvolts)
// MR3: current current (uA)
// MR4: min voltage (uV)
// MR5: max voltage (uV)
// MR6: min current (uA)
// MR7: max current (uA)
// MR8: ramprate (NOT IMPLEMENTED)
#define SDDF_PMIC_GET_REG_INFO_REG_ID (0)
#define SDDF_PMIC_GET_REG_INFO_SUCCESS (0)
#define SDDF_PMIC_GET_REG_INFO_FAIL_INVALID (1)
#define SDDF_PMIC_GET_REG_INFO_ENABLED (1)
#define SDDF_PMIC_GET_REG_INFO_VOLTAGE_UV (2)
#define SDDF_PMIC_GET_REG_INFO_CURRENT_UA (3)
#define SDDF_PMIC_GET_REG_INFO_MIN_VOLTAGE_UV (4)
#define SDDF_PMIC_GET_REG_INFO_MAX_VOLTAGE_UV (5)
#define SDDF_PMIC_GET_REG_INFO_MIN_CURRENT_UA (6)
#define SDDF_PMIC_GET_REG_INFO_MAX_CURRENT_UA (7)
#define SDDF_PMIC_GET_REG_INFO_RAMPRATE (8)

