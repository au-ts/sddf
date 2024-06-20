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

static inline void *sddf_memset(void *s, int c, size_t n)
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

static inline void *sddf_memcpy(void *dest, const void *src, size_t n)
{
// #if __has_builtin(__builtin_memcpy)
//     return __builtin_memcpy(dest, src, n);
// #else
    unsigned char *to = dest;
    const unsigned char *from = src;
    while (n-- > 0) {
        *to++ = *from++;
    }
    return dest;
// #endif
}

static inline char *sddf_strncpy(char *dest, const char *restrict src,
                                 size_t dsize)
{
#if __has_builtin(__builtin_strcpy)
    return __builtin_strncpy(dest, src, dsize);
#else
    char *to = dest;
    while (dsize-- && (*to = *src++)) {
        to++;
    }
    while (dsize--) {
        *to++ = '\0';
    }
    return dest;
#endif
}

static inline int sddf_strcmp(const char *a, const char *b)
{
// #if __has_builtin(__builtin_strcmp)
    // return __builtin_strcmp(a, b);
// #else
    while (*a != '\0' && *b != '\0' && *a == *b) {
        a++;
        b++;
    }
    return (int)(*a) - *b;
// #endif
}

static inline int sddf_strncmp(const char *a, const char *b, size_t n)
{
#if __has_builtin(__builtin_strncmp)
    return __builtin_strncmp(a, b, n);
#else
    for (size_t i = 0; i < n; i++) {
        if (a[i] == '\0' || b[i] == '\0' || a[i] != b[i]) {
            return (int)a[i] - b[i];
        }
    }
    return 0;
#endif
}

static inline char *sddf_strchr(const char *s, int c)
{
#if __has_builtin(__builtin_strncmp)
    return __builtin_strchr(s, c);
#else
    while (*s != '\0') {
        if (*s == c) {
            return s;
        }
        s++;
    }
    if (c == '\0') {
        return s;
    }
    return NULL;
#endif
}

static inline int sddf_memcmp(const void *a, const void *b, size_t n)
{
#if __has_builtin(__builtin_memcmp)
    return __builtin_memcmp(a, b, n);
#else
    unsigned char *_a = a;
    unsigned char *_b = b;
    for (size_t i = 0; i < n; i++) {
        if (_a[i] != _b[i]) {
            return (int)_a[i] - (int)_b[i];
        }
    }
    return 0;
#endif
}


static inline size_t sddf_strlen(const char *s)
{
// #if __has_builtin(__builtin_strlen)
//     return __builtin_strlen(s);
// #else
    const char *_s;
    while (*_s != '\0') {
        _s++;
    }
    return (size_t)(_s - s);
// #endif
}


static inline void *sddf_memmove(void *dest, const void *src, size_t n)
{
#if __has_builtin(__builtin_memmove)
    return __builtin_memmove(dest, src, n);
#else
    if (dest == src) {
        return dest;
    }
    int copy_backwards = dest > src;
    for (size_t i = 0; i < n; i++) {
        if (copy_backwards) {
            dest[n - 1 - i] = src[n - 1 - i];
        } else {
            dest[i] = src[i];
        }
    }
    return dest;
#endif
}
