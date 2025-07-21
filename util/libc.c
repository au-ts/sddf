/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifdef USE_SDDF_LIBC
#include <sddf/util/util.h>
#include <sddf/util/string.h>

int atoi(const char *str) 
{
    return sddf_atoi(str);
}

void *memset(void *s, int c, size_t n) 
{
    return sddf_memset(s, c, n);
}

int memcmp(const void *a, const void *b, size_t n) 
{
    return sddf_memcmp(a, b, n);
}

void *memcpy(void *dest, const void *src, size_t n) 
{
    return sddf_memcpy(dest, src, n);
}

void *memmove(void *dest, const void *src, size_t n) 
{
    return sddf_memmove(dest, src, n);
}

char *strcat(char *restrict dest, const char *restrict src) 
{
    return sddf_strcat(dest, src);
}

int strcmp(const char *a, const char *b) 
{
    return sddf_strcmp(a, b);
}

int strncmp(const char *a, const char *b, size_t n) 
{
    return sddf_strncmp(a, b, n);
}

char *strcpy(char *restrict dest, const char *restrict src) 
{
    return sddf_strcpy(dest, src);
}

size_t strlen(const char *s) 
{
    return sddf_strlen(s);
}

int rand(void)
{
    return sddf_rand();
}

#endif