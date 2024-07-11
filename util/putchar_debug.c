/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sel4/sel4.h>

#define MAX_STRING_LENGTH 0x1000
#define FLUSH_CHAR '\n'

static char string_buffer[MAX_STRING_LENGTH + 1];
static uint32_t local_tail;

void _sddf_puts(const char *s) {
   while (*s) {
        seL4_DebugPutChar(*s);
        s++;
    }
}

void _sddf_putchar(char character)
{
    string_buffer[local_tail] = character;
    local_tail++;

    if (character == FLUSH_CHAR || local_tail == MAX_STRING_LENGTH) {
        string_buffer[local_tail] = '\0';
        _sddf_puts(string_buffer);
        local_tail = 0;
    }
}
