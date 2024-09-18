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
    sddf_printf_("client begin testing pinmux driver:\n");

    bool all_tests_passed = true;
    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x0, PINCTRL_CHIP_AO, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("NULL offset in AO...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("NULL offset in AO...PASS\n");
    }
    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x0, PINCTRL_CHIP_PERIPHERALS, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("NULL offset in periphs...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("NULL offset in periphs...PASS\n");
    }

    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x10, PINCTRL_CHIP_AO, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("AO underflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("AO underflow offset...PASS\n");
    }

    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x24, PINCTRL_CHIP_PERIPHERALS, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("periphs underflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("periphs underflow offset...PASS\n");
    }

    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x3c, PINCTRL_CHIP_AO, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("AO overflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("AO overflow offset...PASS\n");
    }

    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x35c, PINCTRL_CHIP_PERIPHERALS, 0x0) != SDDF_PINCTRL_INVALID_ARGS) {
        sddf_printf_("periphs overflow offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("periphs overflow offset...PASS\n");
    }

    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x15, PINCTRL_CHIP_AO, 0x0) != SDDF_PINCTRL_INVALID_ARGS ||
        sddf_pinctrl_read_mux(PINCTRL_CH, 0x353, PINCTRL_CHIP_PERIPHERALS, 0x0) != SDDF_PINCTRL_INVALID_ARGS
    ) {
        sddf_printf_("unaligned offset...FAIL\n");
        all_tests_passed = false;
    } else {
        sddf_printf_("unaligned offset...PASS\n");
    }

    uint32_t regval;
    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x340, PINCTRL_CHIP_PERIPHERALS, &regval) != SDDF_PINCTRL_SUCCESS) {
        sddf_printf_("read a periphs register...FAIL\n");
        all_tests_passed = false;
    } else {
        if (regval != 0xaebbffff) {
            sddf_printf_("read an periphs register...FAIL, does not match %x != %x\n", regval, 0xaebbffff);
            all_tests_passed = false;
        } else {
            sddf_printf_("read a periphs register...PASS\n");
        }
    }

    if (sddf_pinctrl_read_mux(PINCTRL_CH, 0x30, PINCTRL_CHIP_AO, &regval) != SDDF_PINCTRL_SUCCESS) {
        sddf_printf_("read an AO register...FAIL\n");
        all_tests_passed = false;
    } else {
        if (regval != 0x80040fdc) {
            sddf_printf_("read an AO register...FAIL, does not match %x != %x\n", regval, 0xcfff);
            all_tests_passed = false;
        } else {
            sddf_printf_("read an AO register...PASS\n");
        }
    }

    if (!all_tests_passed) {
        sddf_printf_("some pinmux driver arguments validation tests failed...aborting\n");
        while (true) {};
    } else {
        sddf_printf_("all pinmux driver arguments validation tests passed...continuing\n");
    }
        
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
