/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* A fake Microkit interface */

#pragma once

/* The following macro is to bypass the error branch in include/sddf/util/fence.h
 * for DMA and I/O barriers. These barriers are not handled by GenMC and
 * do not participate in CI.
 */
#define CONFIG_ARCH_X86_64 1
