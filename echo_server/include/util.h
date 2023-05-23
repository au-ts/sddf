/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/sel4.h>

#define UART_REG(x) ((volatile uint32_t *)(UART_BASE + (x)))
#define UART_BASE 0x5000000 //0x30890000 in hardware on imx8mm.
#define STAT 0x98
#define TRANSMIT 0x40
#define STAT_TDRE (1 << 14)

#define ARRAY_SIZE(x) (sizeof(x) / sizeof(x[0]))

#ifdef __GNUC__
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#else
#define likely(x)   (!!(x))
#define unlikely(x) (!!(x))
#endif

static void
putC(uint8_t ch)
{
    while (!(*UART_REG(STAT) & STAT_TDRE)) { }
    *UART_REG(TRANSMIT) = ch;
}

static void
print(const char *s)
{
#ifndef NO_PRINTING
    while (*s) {
        putC(*s);
        s++;
    }
#endif
}

static char
hexchar(unsigned int v)
{
    return v < 10 ? '0' + v : ('a' - 10) + v;
}

static void
puthex64(uint64_t val)
{
    char buffer[16 + 3];
    buffer[0] = '0';
    buffer[1] = 'x';
    buffer[16 + 3 - 1] = 0;
    for (unsigned i = 16 + 1; i > 1; i--) {
        buffer[i] = hexchar(val & 0xf);
        val >>= 4;
    }
    print(buffer);
}

static char
decchar(unsigned int v) {
    return '0' + v;
}

static void
put8(uint8_t x)
{
    char tmp[4];
    unsigned i = 3;
    tmp[3] = 0;
    do {
        uint8_t c = x % 10;
        tmp[--i] = decchar(c);
        x /= 10;
    } while (x);
    print(&tmp[i]);
}

static char*
sel4_strerror(seL4_Word err)
{
    switch (err) {
        case seL4_NoError: return "seL4_NoError";
        case seL4_InvalidArgument: return "seL4_InvalidArgument";
        case seL4_InvalidCapability: return "seL4_InvalidCapability";
        case seL4_IllegalOperation: return "seL4_IllegalOperation";
        case seL4_RangeError: return "seL4_RangeError";
        case seL4_AlignmentError: return "seL4_AlignmentError";
        case seL4_FailedLookup: return "seL4_FailedLookup";
        case seL4_TruncatedMessage: return "seL4_TruncatedMessage";
        case seL4_DeleteFirst: return "seL4_DeleteFirst";
        case seL4_RevokeFirst: return "seL4_RevokeFirst";
        case seL4_NotEnoughMemory: return "seL4_NotEnoughMemory";
    }

    return "<invalid seL4 error>";
}

static void _assert_fail(
    const char  *assertion,
    const char  *file,
    unsigned int line,
    const char  *function)
{
    print("Failed assertion '");
    print(assertion);
    print("' at ");
    print(file);
    print(":");
    put8(line);
    print(" in function ");
    print(function);
    print("\n");
    while (1) {}
}

#ifdef NO_ASSERT

#define assert(expr)

#else

#define assert(expr) \
    do { \
        if (!(expr)) { \
            _assert_fail(#expr, __FILE__, __LINE__, __FUNCTION__); \
        } \
    } while(0)

#endif

