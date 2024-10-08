/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifndef CLK_MEASURE_H_
#define CLK_MEASURE_H_

const char *const *get_msr_clk_list(void);
unsigned long clk_msr(unsigned long clk_mux);

#endif // CLK_MEASURE_H_
