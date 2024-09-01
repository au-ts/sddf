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
    
    bool all_tests_passed = true;
    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x0, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("NULL offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("NULL offset...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x4, 0x0) != SDDF_PINCTRL_INVALID_ARGS ||
        sddf_pinctrl_set_mux(PINCTRL_CH, 0x10, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("mux underflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("mux underflow offset...PASS\n");
    }

#ifdef SOC_IMX8MQ_EVK
    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x534, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
#endif
#ifdef SOC_IMX8MM_EVK
    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x54c, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
#endif
        sddf_printf_("mux overflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("mux overflow offset...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x11d, 0x0) != SDDF_PINCTRL_INVALID_ARGS ||
        sddf_pinctrl_set_mux(PINCTRL_CH, 0x201, 0x0) != SDDF_PINCTRL_INVALID_ARGS
    ) {
        sddf_printf_("unaligned offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("unaligned offset...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0xfffc, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("gpr underflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("gpr underflow offset...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x100c0, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("gpr overflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("gpr overflow offset...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x14, 0x0) != SDDF_PINCTRL_SUCCESS) {
        sddf_printf_("mux write first register...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("mux write first register...PASS\n");
    }

#ifdef SOC_IMX8MQ_EVK
    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x530, 0x0) != SDDF_PINCTRL_SUCCESS) {
#endif
#ifdef SOC_IMX8MM_EVK
    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x548, 0x0) != SDDF_PINCTRL_SUCCESS) {
#endif
        sddf_printf_("mux write last register...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("mux write last register...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x10000, 0x0) != SDDF_PINCTRL_SUCCESS) {
        sddf_printf_("gpr write first register...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("gpr write first register...PASS\n");
    }

    if (sddf_pinctrl_set_mux(PINCTRL_CH, 0x100bc, 0x0) != SDDF_PINCTRL_SUCCESS) {
        sddf_printf_("gpr write last register...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("gpr write last register...PASS\n");
    }

    if (!all_tests_passed) {
        sddf_printf_("some pinmux driver arguments validation tests failed...aborting\n");
        while (true) {};
    } else {
        sddf_printf_("all pinmux driver arguments validation tests passed...continuing\n");
        sddf_pinctrl_reset(PINCTRL_CH);
    }

    // Correct console output:
    // client begin testing pinmux driver args validation:
    // PINCTRL DRIVER|ERROR: offset is out of bound
    // NULL offset...PASS
    // PINCTRL DRIVER|ERROR: offset is out of bound
    // PINCTRL DRIVER|ERROR: offset is out of bound
    // mux underflow offset...PASS
    // PINCTRL DRIVER|ERROR: offset is out of bound
    // mux overflow offset...PASS
    // PINCTRL DRIVER|ERROR: offset is not 4 bytes aligned
    // PINCTRL DRIVER|ERROR: offset is not 4 bytes aligned
    // unaligned offset...PASS
    // PINCTRL DRIVER|ERROR: offset is out of bound
    // gpr underflow offset...PASS
    // PINCTRL DRIVER|ERROR: offset is out of bound
    // gpr overflow offset...PASS
    // mux write first register...PASS
    // mux write last register...PASS
    // gpr write first register...PASS
    // gpr write last register...PASS
    // all pinmux driver arguments validation tests passed...continuing
        
    sddf_printf_("client hello #%lu\n", echo_number);
    sddf_timer_set_timeout(1, NS_IN_S);
}

void notified(microkit_channel ch) {
    if (ch == TIMER_CH) {
        echo_number += 1;
        // 1 sec timer has expired, echo then set pinmux for UART1TX

#ifdef SOC_IMX8MQ_EVK
        if (echo_number % 2 == 0) {
            // Connect UART1_TXD pad to the UART1 device
            sddf_pinctrl_reset(PINCTRL_CH);
        } else {
            // Connect UART1_TXD pad to the SPI device. You will not see the output for odd numbers
            sddf_pinctrl_set_mux(PINCTRL_CH, 0x238, 0x1);
        }
#endif

#ifdef SOC_IMX8MM_EVK
        // For some obscure reason IMX8MM on machine queue uses UART2 instead of UART1 for debug output.
        if (echo_number % 2 == 0) {
            // Connect UART2_TXD pad to the UART2 device
            sddf_pinctrl_reset(PINCTRL_CH);
        } else {
            // Connect UART2_TXD pad to the SPI device. You will not see the output for odd numbers
            sddf_pinctrl_set_mux(PINCTRL_CH, 0x240, 0x1);
        }
#endif

        sddf_printf_("client hello #%lu\n", echo_number);
        sddf_timer_set_timeout(1, NS_IN_S);
    }
}
