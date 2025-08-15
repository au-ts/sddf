/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/util/util.h>
#include <string.h>

int atoi(const char *str)
{
    return sddf_atoi(str);
}

#undef strcat
char *strcat(char *restrict dest, const char *restrict src)
{
    char *to = dest;
    while (*to) {
        to++;
    };
    strcpy(to, src);
    return dest;
}
