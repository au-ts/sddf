/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/util/printf.h>

static char cml_memory[1024 * 20];
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern void cml_main(void);

void cml_exit(int arg)
{
    sddf_dprintf("ERROR! We should not be getting here\n");
}

void cml_err(int arg)
{
    if (arg == 3) {
        sddf_dprintf("Memory not ready for entry. You may have not run the init code yet, or be trying to enter "
                     "during an FFI call.\n");
    }
    cml_exit(arg);
}

void cml_clear()
{
    sddf_dprintf("Trying to clear cache\n");
}

void init_pancake_mem()
{
    unsigned long cml_heap_sz = 1024 * 10;
    unsigned long cml_stack_sz = 1024 * 10;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;
}
