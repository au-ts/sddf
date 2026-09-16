/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <sddf/util/pancake_common.h>
#include <sddf/util/printf.h>
#include <sddf/util/util.h>

static uintptr_t cml_memory[1024 * 20 / sizeof(uintptr_t)];
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

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

void cml_clear(void)
{
    sddf_dprintf("Trying to clear cache.\n");
}

void init_pancake_mem()
{
    unsigned long cml_heap_sz = 1024 * 10;
    unsigned long cml_stack_sz = 1024 * 10;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;

    /* All cml_* pointers must be word aligned. */
    assert((uintptr_t) cml_heap % sizeof(uintptr_t) == 0);
    assert((uintptr_t) cml_stack % sizeof(uintptr_t) == 0);
    assert((uintptr_t) cml_stackend % sizeof(uintptr_t) == 0);
}
