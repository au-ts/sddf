/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

const char *const *get_msr_clk_list(void);
unsigned long clk_msr(unsigned long clk_mux);
