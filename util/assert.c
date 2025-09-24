/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <sddf/util/printf.h>

/** Our dprintf() functions will sometimes go through our standard printf()
 *  machinery, which includes assert() statements itself. In the case that
 *  the machinery is failing, this would lead to infinite recursion and an
 *  eventual stack overflow. By saving whether or not we were previously
 *  perform an _assert_fail, and by having two different trap paths, we can
 *  identify assertion failures due to this.
 */
static bool currently_asserting = false;

void _assert_fail(const char  *assertion, const char  *file, unsigned int line, const char  *function)
{
    bool previously_asserting = currently_asserting;
    currently_asserting = true;

    if (previously_asserting) {
        __builtin_trap();
    }

    sddf_dprintf("Failed assertion '%s' at %s:%u in function %s\n", assertion, file, line, function);
    __builtin_trap();
}
