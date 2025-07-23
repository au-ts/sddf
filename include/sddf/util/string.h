/*
 * Declarations for a subset of the C standard library string functions.
 *
 * Copyright 2024 UNSW, Sydney
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once
#include <stddef.h>

extern void *sddf_memset(void *s, int c, size_t n);
extern void *sddf_memcpy(void *dest, const void *src, size_t n);
extern char *sddf_strcpy(char *restrict dest, const char *restrict src);
extern char *sddf_strncpy(char *dest, const char *restrict src, size_t dsize);
extern int sddf_strcmp(const char *a, const char *b);
extern int sddf_strncmp(const char *a, const char *b, size_t n);
extern char *sddf_strchr(const char *s, int c);
extern int sddf_memcmp(const void *a, const void *b, size_t n);
extern size_t sddf_strlen(const char *s);
extern void *sddf_memmove(void *dest, const void *src, size_t n);

static inline char *sddf_strcat(char *restrict dest, const char *restrict src)
{
    char *to = dest;
    while (*to) {
        to++;
    };
    sddf_strcpy(to, src);
    return dest;
}
