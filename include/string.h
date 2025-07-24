/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stddef.h>

void *memset(void *s, int c, size_t n);
int memcmp(const void *a, const void *b, size_t n);
void *memcpy(void *dest, const void *src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
char *strcat(char *restrict dest, const char *restrict src);
int strcmp(const char *a, const char *b);
int strncmp(const char *a, const char *b, size_t n);
char *strcpy(char *restrict dest, const char *restrict src);
size_t strlen(const char *s);