/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <sddf/util/shadow_cnode.h>

/* Map a memory region at the given physical address and size to the given virtual address.
 * The mapping rights and attributes are given by the caller.
 * The physical and virtual addresses, and size must be aligned on a small page boundary.
 * This may fail if there is no or not enough UTs that can satisfy the allocation. */
bool map_memory_region(shadow_cnode_t *shadow_cnode, seL4_CPtr vspace_cptr, uintptr_t paddr, size_t size,
                       uintptr_t vaddr, seL4_CapRights_t rights, seL4_X86_VMAttributes vm_attr);
