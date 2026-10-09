/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/util/ialloc.h>

/* A utility library for managing CNode. */

#define MAX_SHADOW_CNODE_SIZE_BITS 11u /* 2**11 = 2048 slots */

/* The kernel does not expose a consistent enum for cap type, unlike object which have seL4_ObjectType and
 * seL4_seL4ArchObjectType so we need to have this.
 * Note that it is a better design if we track objects and caps to them separately. */
typedef enum {
    CAP_TYPE_NONE = 0,
    CAP_TYPE_CNODE_SELF,
    CAP_TYPE_UT,
    CAP_TYPE_NTFN,
    CAP_TYPE_SMALL_PAGE,
    CAP_TYPE_LARGE_PAGE,
    CAP_TYPE_PAGE_TABLE,
    CAP_TYPE_IRQ,
    CAP_TYPE_IRQ_CONTROL,
    CAP_TYPE_X86_IO_PORT,
    CAP_TYPE_X86_IO_PORT_CONTROL,
    CAP_TYPE_MAX,
} shadow_cap_type_t;

#define PARENT_CSLOT_NONE UINT32_MAX

typedef struct {
    uint64_t watermark;
    uint8_t is_device;
} shadow_ut_t;

typedef struct {
    shadow_cap_type_t type;
    uint64_t base_paddr;
    uint64_t end_paddr;
    uint32_t parent_cslot;
    uint64_t cookie;

    union {
        shadow_ut_t as_ut;
    };
} shadow_cap_t;

#define SHADOW_CNODE_MAKE_CAP(type_, base_paddr_, end_paddr_, parent_cslot_, cookie_) \
        ((shadow_cap_t) { \
            .type = type_, \
            .base_paddr = base_paddr_, \
             .end_paddr = end_paddr_, \
             .parent_cslot = parent_cslot_, \
             .cookie = cookie_ \
            })

typedef struct {
    shadow_cap_t caps[BIT(MAX_SHADOW_CNODE_SIZE_BITS)];
    size_t num_slots;
    seL4_CPtr cnode_cptr;
} shadow_cnode_t;

bool shadow_cnode_init(shadow_cnode_t *shadow_cnode, uint8_t size_bits, seL4_CPtr cnode_cptr);

bool shadow_cnode_insert_cap_at_slot(shadow_cnode_t *shadow_cnode, shadow_cap_t *cap, size_t cslot);

bool shadow_cnode_find_free_slot(shadow_cnode_t *shadow_cnode, size_t *ret);

shadow_cap_t *shadow_cnode_get_cap_at_slot(shadow_cnode_t *shadow_cnode, size_t cslot);

bool shadow_cnode_find_cap_slot_of_type(shadow_cnode_t *shadow_cnode, shadow_cap_type_t type, size_t *cslot);

shadow_cap_t *shadow_cnode_get_caps_table(shadow_cnode_t *shadow_cnode, size_t *num_slots);

bool shadow_cnode_delete_cap_at_slot(shadow_cnode_t *shadow_cnode, size_t cslot);

seL4_CPtr shadow_cnode_cslot_to_cptr(shadow_cnode_t *shadow_cnode, size_t cslot);

/* Given the `target_paddr` and the object's `size_bits`,
 * attempt to create the object of type `object_type`
 * at the required paddr.
 * `size_bits` is a required argument for creating UT. */
bool shadow_cnode_retype_at_paddr(shadow_cnode_t *shadow_cnode, seL4_Word target_paddr, seL4_Word object_type,
                                  seL4_Word size_bits, size_t *retyped_cslot);

/* Similar to shadow_cnode_retype_at_paddr(), but it will create the object from any
 * non-device untyped that fits. Since it is unusual that you want a frame from any
 * device UT. */
bool shadow_cnode_retype(shadow_cnode_t *shadow_cnode, seL4_Word object_type, seL4_Word size_bits,
                         size_t *retyped_cslot);

const char *shadow_cap_type_to_string(shadow_cap_type_t type);