/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// This header file defines the state machine used by the driver to function.
#pragma once
#include <sddf/pmic/protocol.h>
#include <sddf/util/util.h>
#include <microkit.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sddf/util/printf.h>
#include <sddf/i2c/queue.h>


#define DEBUG_PMIC_DRIVER
#ifdef DEBUG_PMIC_DRIVER
#define LOG_PMIC_DRIVER(...) do{ sddf_dprintf("PMIC DRIVER|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_PMIC_DRIVER(...) do{}while(0)
#endif

#define LOG_PMIC_DRIVER_ERR(...) do{ sddf_dprintf("PMIC DRIVER|ERROR: "); sddf_dprintf(__VA_ARGS__); }while(0)

// Utility types
typedef uint32_t pmic_unit_t;
typedef uint32_t pmic_reg_id_t;

typedef struct unit_capability {
    bool adjustable;
    pmic_unit_t min_value;
    pmic_unit_t max_value;
    pmic_unit_t quantisation;  // Number of bits used to parameterise value in PMIC - i.e. conf reg size
} unit_capability_t;

typedef struct reg_capabilities {
    unit_capability_t voltage;
    unit_capability_t current;
    bool toggleable;    // Can this regulator be turned on and off?
} reg_capabilities_t;

typedef struct sddf_regulator {
    reg_capabilities_t capabilities;
    pmic_unit_t voltage_uv;
    pmic_unit_t current_ua;
    bool enabled;
} sddf_regulator_t;

typedef struct pmic_driver_state {
    microkit_channel curr_client;
    uint64_t curr_ppc_op;
    uint64_t err;
    uint64_t get_info_cnt;  // Progress through get info call. Easier to count than add N states!
} pmic_driver_state_t;

// typedef enum { S_IDLE, S_REQ_RET, NUM_STATES } pmic_state_t;

// State machine:
// Idle: sleeping
// Request: a PPC has arrived and we've dispatched an I2C command to handle it
//          This state is IMPLICIT. We are here by merit of a PPC arriving.
// // Request return: notification has arrived from I2C, finish PPC and go to sleep.
// // Invariant: one I2C request per PPC only, allowing state machine to be simple.
//
// typedef struct fsm {
//     pmic_state_t curr_state;
//     pmic_state_t next_state;
//     bool yield; // fsm funcs can set this to tell the FSM loop to allow the PD to sleep
// } fsm_data_t;
//
// // Each state implements a single state function which is called by the FSM.
// typedef void pmic_state_func_t(fsm_data_t *fsm, pmic_driver_state_t *state);
//
// Prototype for FSM function
// void fsm(fsm_data_t *f);
//
// void state_idle(fsm_data_t *fsm, pmic_driver_state_t *state);
// void state_req(fsm_data_t *fsm, pmic_driver_state_t *state);
// void state_req_return(fsm_data_t *fsm, pmic_driver_state_t *state);

// PPC handlers
sddf_pmic_err_t pmic_drv_enable_reg(uint64_t reg_id);
sddf_pmic_err_t pmic_drv_disable_reg(uint64_t reg_id);
sddf_pmic_err_t pmic_drv_set_vout(uint64_t reg_id, uint64_t voltage_uv);
sddf_pmic_err_t pmic_drv_set_climit(uint64_t reg_id, uint64_t current_ua);
sddf_pmic_err_t pmic_drv_get_info(uint64_t reg_id, sddf_pmic_reg_info_t *info);

static void pmic_reset_state(pmic_driver_state_t *s)
{
    memset(s, 0, sizeof(pmic_driver_state_t));
    s->curr_ppc_op = SDDF_PMIC_PPC_INVALID;
    // HACK: sentinel value due to HACK required for i2c-based pmics.
}

