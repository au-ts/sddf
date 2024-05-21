/*
 * Very simple string.h that punts everything to compiler builtins.
 * This is what usually happens for -O3, but we want it for everything.
 *
 * Copyright 2024 UNSW, Sydney
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stddef.h>

#ifndef __has_builtin
#  define __has_builtin(x) 0
#endif

static inline void *memset(void *s, int c, size_t n)
{
#if __has_builtin(__builtin_memset)
    return __builtin_memset(s, c, n);
#else
    unsigned char *p = s;
    while (n-- > 0) {
        *p++ = c;
    }
    return s;
#endif
}

static inline void *memcpy(void *dest, const void *src, size_t n)
{
#if __has_builtin(__builtin_memcpy)
    return __builtin_memcpy(dest, src, n);
#else
    unsigned char *to = dest;
    const unsigned char *from = src;
    while (n-- > 0) {
        *to++ = *from++;
    }
    return dest;
#endif
}

static inline char *strncpy (char *dest, const char *restrict src,
                             size_t dsize)
{
#if __has_builtin(__builtin_strcpy)
    return __builtin_strncpy(dest, src, dsize);
#else
    char *to = dest;
    while (dsize-- && (*to = *src++)) {
        to++;
    }
    *to = '\0';
    while (dsize--) {
        *to++ = '\0';
    }
    return dest;
#endif
}

static inline int strcmp(const char *a, const char *b)
{
#if __has_builtin(__builtin_strcmp)
    return __builtin_strcmp(a, b);
#else
#   error Need a strcmp implementation
#endif
}

static inline int strncmp(const char *a, const char *b, size_t n)
{
#if __has_builtin(__builtin_strncmp)
    return __builtin_strncmp(a, b, n);
#else
#   error Need a strncmp implementation
#endif
}

static inline char *strchr(const char *s, int c)
{
#if __has_builtin(__builtin_strncmp)
    return __builtin_strchr(s, c);
#else
#   error Need a strchr implementation
#endif
}

static inline int memcmp(const void *a, const void *b, size_t n)
{
#if __has_builtin(__builtin_strcmp)
    return __builtin_memcmp(a, b, n);
#else
#   error Need a memcmp implementation
#endif
}


static inline size_t strlen(const char *s)
{
#if __has_builtin(__builtin_strlen)
    return __builtin_strlen(s);
#else
#   error Need a strlen implementation
#endif
}


static inline void *memmove(void *dest, const void *src, size_t n)
{
#if __has_builtin(__builtin_memmove)
    return __builtin_memmove(dest, src, n);
#else
#   error Need a memmove implementation
#endif
}
