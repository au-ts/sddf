/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>

#include <microkit.h>
#include <sddf/util/printf.h>
#include <sddf/timer/client.h>
#include <sddf/timer/protocol.h>
#include <sddf/pinctrl/client.h>

#define PINCTRL_CH 0
#define TIMER_CH 1

uint64_t echo_number = 0;

void init(void) {
    sddf_printf_("client begin testing pinmux driver args validation:\n");
    
//     bool all_tests_passed = true;
//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x0, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
//         sddf_printf_("NULL offset...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("NULL offset...PASS\n");
//     }

//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x4, 0x0) != SDDF_PINCTRL_INVALID_ARGS ||
//         sddf_pinctrl_read_mux(PINCTRL_CH, 0x10, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
//         sddf_printf_("mux underflow offset...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("mux underflow offset...PASS\n");
//     }

// #ifdef SOC_IMX8MQ_EVK
//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x534, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
// #endif
// #ifdef SOC_IMX8MM_EVK
//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x54c, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
// #endif
//         sddf_printf_("mux overflow offset...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("mux overflow offset...PASS\n");
//     }

//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x11d, 0x0) != SDDF_PINCTRL_INVALID_ARGS ||
//         sddf_pinctrl_read_mux(PINCTRL_CH, 0x201, 0x0) != SDDF_PINCTRL_INVALID_ARGS
//     ) {
//         sddf_printf_("unaligned offset...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("unaligned offset...PASS\n");
//     }

//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0xfffc, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
//         sddf_printf_("gpr underflow offset...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("gpr underflow offset...PASS\n");
//     }

//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x100c0, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
//         sddf_printf_("gpr overflow offset...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("gpr overflow offset...PASS\n");
//     }

//     uint32_t discard;
//     if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x14, &discard) != SDDF_PINCTRL_SUCCESS) {
//         sddf_printf_("mux read first register...FAIL\n");
//         all_tests_passed = false;
//     } else {
//         sddf_printf_("mux read first register...PASS\n");
//     }

//     if (!all_tests_passed) {
//         sddf_printf_("some pinmux driver arguments validation tests failed...aborting\n");
//         while (true) {};
//     } else {
//         sddf_printf_("all pinmux driver arguments validation tests passed...continuing\n");
//     }
        
    sddf_printf_("client hello #%lu\n", echo_number);
    sddf_timer_set_timeout(1, NS_IN_S);
}

void notified(microkit_channel ch) {
    if (ch == TIMER_CH) {
        echo_number += 1;

        sddf_printf_("client hello #%lu\n", echo_number);
        sddf_timer_set_timeout(1, NS_IN_S);
    }
}
