/*
 * Copyright 2026, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stddef.h>
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
    sddf_dprintf("Pancake program exited.\n");
    /* trap because both cml_exit() and cml_err() should not be called
     * for normal Pancake programs
     */
    assert(false);
}

void cml_err(int arg)
{
    if (arg == 3) {
        sddf_dprintf("CakeML Memory not ready for entry. "
                     "You may have not run the init code yet, "
                     "or be trying to enter during an FFI call.\n");
    }
    cml_exit(arg);
}

#ifdef CONFIG_ARCH_X86_64
void cml_clear(void)
{
    sddf_dprintf("Trying to clear cache.\n");
    /* trap because sddf components are statically compiled,
     * and this function should not be called
     */
    assert(false);
}

void *cml_install(uint8_t *src, size_t len, uint8_t *dest) {
    sddf_dprintf("Trying to install code.\n");
    /* trap because sddf components are statically compiled,
     * and this function should not be called
     */
    assert(false);
    return NULL;
}
#endif

void init_pancake_mem()
{
    unsigned long cml_heap_sz = 1024 * 10;
    unsigned long cml_stack_sz = 1024 * 10;
    cml_heap = cml_memory;
    cml_stack = cml_heap + cml_heap_sz;
    cml_stackend = cml_stack + cml_stack_sz;

    /* All cml_* pointers must be word aligned. */
    assert((uintptr_t)cml_heap % sizeof(uintptr_t) == 0);
    assert((uintptr_t)cml_stack % sizeof(uintptr_t) == 0);
    assert((uintptr_t)cml_stackend % sizeof(uintptr_t) == 0);
}
