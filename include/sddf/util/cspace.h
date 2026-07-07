/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>

#define MAX_NUM_CAP_SLOTS 512

/* #define IDX_TO_CPTR(idx) (seL4_CPtr)(cnode_cptr_remaining_untypeds + idx) */
#define IDX_TO_CPTR(cnode_list, idx) (seL4_CPtr)(cnode_list.cptr + idx)
#define GET_OBJECT_SIZE(object_type, size_bits) (1ULL << get_object_size_bits(object_type, size_bits));
#define PAGE_SIZE GET_OBJECT_SIZE(seL4_X86_64, 0)

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

// TODO: check if this makes sense to go to libsel4
// https://github.com/seL4/seL4_libs/blob/master/libsel4vka/arch_include/x86/vka/arch/object.h#L62
uint8_t get_object_size_bits(seL4_Word object_type, seL4_Word size_bits)
{
    switch (object_type) {
    /* Generic objects. */
    case seL4_UntypedObject:
        return size_bits;
    case seL4_TCBObject:
        return seL4_TCBBits;
    case seL4_EndpointObject:
        return seL4_EndpointBits;
    case seL4_NotificationObject:
        return seL4_NotificationBits;
    case seL4_CapTableObject:
        return (seL4_SlotBits + size_bits);
    case seL4_X86_4K:
        return seL4_PageBits;
    case seL4_X86_LargePageObject:
        return seL4_LargePageBits;
    case seL4_X86_PageTableObject:
        return seL4_PageTableBits;
    case seL4_X86_PageDirectoryObject:
        return seL4_PageDirBits;
    default:
        // TODO: double-check this
        return size_bits;
    }
}
