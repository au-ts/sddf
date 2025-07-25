/*
 * Declarations for a subset of the C standard library string functions.
 *
 * Copyright 2024 UNSW, Sydney
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stddef.h>
#include <string.h>

static inline void *sddf_memset(void *s, int c, size_t n)
{
    return memset(s, c, n);
}

static inline void *sddf_memcpy(void *dest, const void *src, size_t n)
{
    return memcpy(dest, src, n);
}

static inline char *sddf_strcpy(char *restrict dest, const char *restrict src)
{
    return strcpy(dest, src);
}

static inline int sddf_strcmp(const char *a, const char *b)
{
    return strcmp(a, b);
}

static inline int sddf_strncmp(const char *a, const char *b, size_t n)
{
    return strncmp(a, b, n);
}

static inline int sddf_memcmp(const void *a, const void *b, size_t n)
{
    return memcmp(a, b, n);
}

static inline size_t sddf_strlen(const char *s)
{
    return strlen(s);
}

static inline void *sddf_memmove(void *dest, const void *src, size_t n)
{
    return memmove(dest, src, n);
}
