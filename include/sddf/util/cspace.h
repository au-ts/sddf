/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>

#define MAX_NUM_CAP_SLOTS 512

/* #define IDX_TO_CPTR(idx) (seL4_CPtr)(cnode_cptr_remaining_untypeds + idx) */
#define IDX_TO_CPTR(cnode_specs, idx) (seL4_CPtr)(cnode_specs->cptr + idx)
#define GET_OBJECT_SIZE(object_type, size_bits) (1ULL << get_object_size_bits(object_type, size_bits))

typedef struct {
    uintptr_t base_addr;
    uintptr_t end_addr;
    uint8_t is_device;
    uint8_t object_type;
    uint32_t parent;
    uint32_t child;
    uint32_t next;
} cap_desc_t;

typedef struct {
    cap_desc_t caps[MAX_NUM_CAP_SLOTS];
    uint32_t start;         // start index
    uint32_t end;           // end index
    uint32_t active_ut_idx; // Index of untyped to be allocated for kernel objects
    seL4_CPtr cptr;         // CNode capability address
} cnode_specs_t;

uint8_t get_object_size_bits(seL4_Word object_type, seL4_Word size_bits);

void update_active_ut_idx(cnode_specs_t *cnode_specs);

seL4_Error cnode_untypeds_revoke(cnode_specs_t *cnode_specs);

seL4_Error retype_at_paddr(cnode_specs_t *cnode_specs,
                           seL4_Word target_paddr,
                           seL4_Word object_type,
                           seL4_Word size_bits,
                           uint32_t *retyped_cptr_idx);

seL4_Error untyped_retype(cnode_specs_t *cnode_specs,
                          uint32_t ut_idx,
                          seL4_Word object_type,
                          seL4_Word size_bits,
                          uint32_t *retyped_cap_idx);

bool update_cnode_specs_after_revoke(cnode_specs_t *cnode_specs,
                                     uint32_t ut_idx);
