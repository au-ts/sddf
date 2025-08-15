/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stddef.h>

#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#if __has_builtin(__builtin_memset)
#define memset __builtin_memset
#else
void *memset(void *s, int c, size_t n);
#endif

#if __has_builtin(__builtin_memcmp)
#define memcmp __builtin_memcmp
#else
int memcmp(const void *a, const void *b, size_t n);
#endif

#if __has_builtin(__builtin_memcpy)
#define memcpy __builtin_memcpy
#else
void *memcpy(void *dest, const void *src, size_t n);
#endif

#if __has_builtin(__builtin_memmove)
#define memmove __builtin_memmove
#else
void *memmove(void *dest, const void *src, size_t n);
#endif

#if __has_builtin(__builtin_strcat)
#define strcat __builtin_strcat
#else
char *strcat(char *restrict dest, const char *restrict src);
#endif

#if __has_builtin(__builtin_strcmp)
#define strcmp __builtin_strcmp
#else
int strcmp(const char *a, const char *b);
#endif

#if __has_builtin(__builtin_strncmp)
#define strncmp __builtin_strncmp
#else
int strncmp(const char *a, const char *b, size_t n);
#endif

#if __has_builtin(__builtin_strcpy)
#define strcpy __builtin_strcpy
#else
char *strcpy(char *restrict dest, const char *restrict src);
#endif

#if __has_builtin(__builtin_strlen)
#define strlen __builtin_strlen
#else
size_t strlen(const char *s);
#endif
