/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// arm_barriers.h — explicit ARM/AArch64 barriers for MMIO work

#pragma once

#if defined(__aarch64__) || defined(__arm__)
#define DMB_ISHST()  __asm__ __volatile__("dmb ishst" ::: "memory")
#define DMB_ISH()    __asm__ __volatile__("dmb ish"   ::: "memory")
#define DSB_ISHST()  __asm__ __volatile__("dsb ishst" ::: "memory")
#define DSB_ISH()    __asm__ __volatile__("dsb ish"   ::: "memory")
#else
#error "arm_barriers.h included on non-ARM target"
#endif
