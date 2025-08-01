/*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2001-2003 Swedish Institute of Computer Science.
 */
#pragma once

#include <stdint.h>
#include <sys/types.h>
#include <sddf/util/printf.h>

typedef  uint8_t  u8_t;
typedef uint16_t u16_t;
typedef uint32_t u32_t;
typedef uint64_t u64_t;

typedef  int8_t   s8_t;
typedef int16_t  s16_t;
typedef int32_t  s32_t;
typedef int64_t  s64_t;

typedef uintptr_t mem_ptr_t;

#ifndef SSIZE_MAX
/* Whilst ssize_t is defined by sys/types.h, at least on aarch64-none-elf GCC
   version 14.2.1 SSIZE_MAX is not defined.

   If SSIZE_MAX is not defined then we take (SIZE_MAX - 1)/2 under the
   assumption that ssize_t and size_t are related in the standard way.
*/
#define SSIZE_MAX ((SIZE_MAX - 1) >> 1)
#endif

#define U16_F "hu"
#define S16_F "d"
#define X16_F "hx"
#define U32_F "u"
#define S32_F "d"
#define X32_F "x"
#define SZT_F "lu"


// BYTE_ORDER might be defined by the architecture
#ifndef BYTE_ORDER
#if defined(__BYTE_ORDER__)
#  define BYTE_ORDER __BYTE_ORDER__
#elif defined(__BIG_ENDIAN)
#  define BYTE_ORDER BIG_ENDIAN
#elif defined(__LITTLE_ENDIAN)
#  define BYTE_ORDER LITTLE_ENDIAN
#else
#  error Unable to detemine system endianess
#endif
#endif


#define LWIP_CHKSUM_ALGORITHM 3

#define PACK_STRUCT_STRUCT __attribute__((packed))
#define PACK_STRUCT_BEGIN
#define PACK_STRUCT_END


#define LWIP_PLATFORM_BYTESWAP 1
#define LWIP_PLATFORM_HTONS(x) ( (((u16_t)(x))>>8) | (((x)&0xFF)<<8) )
#define LWIP_PLATFORM_HTONL(x) ( (((u32_t)(x))>>24) | (((x)&0xFF0000)>>8) \
                               | (((x)&0xFF00)<<8) | (((x)&0xFF)<<24) )

#define LWIP_RAND                       rand

/* Plaform specific diagnostic output */
#define LWIP_PLATFORM_DIAG(x)           \
        do {                            \
            sddf_printf x ;\
        } while(0)

#define LWIP_PLATFORM_ASSERT(x) \
        do {                                                    \
            sddf_printf("Assertion failed: %s\n", #x);              \
            while(1);                                           \
        } while(0)
