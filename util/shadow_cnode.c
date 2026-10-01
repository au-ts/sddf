/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sddf/util/ialloc.h>
#include <sddf/util/printf.h>
#include <sddf/util/custom_libc/string.h>
#include <sddf/util/shadow_cnode.h>

#define LOG_ERR(fmt, ...) \
    sddf_dprintf("SHADOW CNODE %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)

bool shadow_cnode_insert_cap_at_slot(shadow_cnode_t *shadow_cnode, shadow_cap_t *cap, size_t cslot)
{
    if (cslot >= shadow_cnode->num_slots) {
        LOG_ERR("slot %lu is out of bound, max is %lu\n", cslot, shadow_cnode->num_slots);
        return false;
    }

    if (shadow_cnode->caps[cslot].type != CAP_TYPE_NONE) {
        LOG_ERR("slot %lu is taken\n", cslot);
        return false;
    }

    if (cap->type >= CAP_TYPE_MAX || cap->type == CAP_TYPE_NONE) {
        LOG_ERR("invalid cap type %u given\n", cap->type);
        return false;
    }

    memcpy(&shadow_cnode->caps[cslot], cap, sizeof(shadow_cap_t));
    return true;
}

bool shadow_cnode_find_free_slot(shadow_cnode_t *shadow_cnode, size_t *ret)
{
    /* @billn not ideal, use fsmalloc or something */
    for (size_t i = 0; i < shadow_cnode->num_slots; i++) {
        if (shadow_cnode->caps[i].type == CAP_TYPE_NONE) {
            *ret = i;
            return true;
        }
    }
    return false;
}

seL4_CPtr shadow_cnode_cslot_to_cptr(shadow_cnode_t *shadow_cnode, size_t cslot)
{
    return shadow_cnode->cnode_cptr + cslot;
}

shadow_cap_t *shadow_cnode_get_cap_at_slot(shadow_cnode_t *shadow_cnode, size_t cslot)
{
    if (cslot >= shadow_cnode->num_slots) {
        LOG_ERR("slot %lu is out of bound, max is %lu\n", cslot, shadow_cnode->num_slots);
        return NULL;
    }

    return &shadow_cnode->caps[cslot];
}

bool shadow_cnode_find_cap_slot_of_type(shadow_cnode_t *shadow_cnode, shadow_cap_type_t type, size_t *cslot)
{
    if (type >= CAP_TYPE_MAX || type == CAP_TYPE_NONE) {
        LOG_ERR("invalid cap type %u given\n", type);
        return false;
    }

    for (size_t i = 0; i < shadow_cnode->num_slots; i++) {
        if (shadow_cnode->caps[i].type == type) {
            *cslot = i;
            return true;
        }
    }

    return false;
}

bool shadow_cnode_delete_cap_at_slot(shadow_cnode_t *shadow_cnode, size_t cslot)
{
    if (cslot >= shadow_cnode->num_slots) {
        LOG_ERR("slot %lu is out of bound, max is %lu\n", cslot, shadow_cnode->num_slots);
        return false;
    }

    memset(&shadow_cnode->caps[cslot], 0, sizeof(shadow_cap_t));
    return true;
}

bool shadow_cnode_init(shadow_cnode_t *shadow_cnode, uint8_t size_bits, seL4_CPtr cnode_cptr)
{
    if (size_bits > MAX_SHADOW_CNODE_SIZE_BITS) {
        LOG_ERR("cannot initialise with %u size bits, max is %u\n", size_bits, MAX_SHADOW_CNODE_SIZE_BITS);
        return false;
    }

    memset(shadow_cnode, 0, sizeof(shadow_cnode_t));

    shadow_cnode->num_slots = BIT(size_bits);
    shadow_cnode->cnode_cptr = cnode_cptr;

    shadow_cnode_insert_cap_at_slot(shadow_cnode,
                                    &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_CNODE_SELF, 0, 0, PARENT_CSLOT_NONE, 0), 0);

    return true;
}

// TODO: check if this makes sense to go to libsel4
// https://github.com/seL4/seL4_libs/blob/master/libsel4vka/arch_include/x86/vka/arch/object.h#L62
static uint8_t get_object_size_bits(seL4_Word object_type, uint8_t size_bits)
{
    switch (object_type) {
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
    case seL4_X86_PDPTObject:
        return seL4_PDPTBits;
    default:
        return 0;
    }
}

static bool get_untyped_containing_paddr(shadow_cnode_t *shadow_cnode, seL4_Word target_paddr, size_t *target_ut_idx)
{
    size_t i = 0;
    for (; i < shadow_cnode->num_slots; i++) {
        shadow_cap_t *cap = &shadow_cnode->caps[i];
        if (cap->type == CAP_TYPE_UT && target_paddr >= cap->as_ut.watermark && target_paddr < cap->end_paddr) {
            break;
        }
    }

    if (i == shadow_cnode->num_slots) {
        LOG_ERR("UT containing physical address 0x%lx can't be found\n", target_paddr);
        return false;
    }

    *target_ut_idx = i;
    return true;
}

static shadow_cap_type_t sel4_obj_type_to_shadow_cap_type(seL4_Word object_type)
{
    switch (object_type) {
    case seL4_UntypedObject:
        return CAP_TYPE_UT;
    case seL4_X86_4K:
        return CAP_TYPE_SMALL_PAGE;
    case seL4_X86_LargePageObject:
        return CAP_TYPE_LARGE_PAGE;
    case seL4_X86_PageTableObject:
    case seL4_X86_PageDirectoryObject:
    case seL4_X86_PDPTObject:
        return CAP_TYPE_PAGE_TABLE;
    default:
        LOG_ERR("unimplemented obj type %lu\n", object_type);
        return CAP_TYPE_NONE;
    }
}

static bool untyped_retype(shadow_cnode_t *shadow_cnode, size_t ut_cslot, seL4_Word object_type, uint8_t size_bits,
                           size_t *retyped_cslot)
{
    assert(size_bits);

    shadow_cap_t *ut = &shadow_cnode->caps[ut_cslot];
    if (ut->type != CAP_TYPE_UT) {
        LOG_ERR("slot %lu is not an untyped\n", ut_cslot);
        return false;
    }

    /* The kernel places the object at the watermark rounded up to the object size */
    uint64_t start = ROUND_UP(ut->as_ut.watermark, BIT(size_bits));
    uint64_t end = start + BIT(size_bits);
    if (end > ut->end_paddr) {
        LOG_ERR("UT %lu can't fit a %u-bit object\n", ut_cslot, size_bits);
        return false;
    }

    size_t destination_cslot;
    if (!shadow_cnode_find_free_slot(shadow_cnode, &destination_cslot)) {
        LOG_ERR("Out of space in CNode UT retype.\n");
        return false;
    }

    // @terryb: need to update this if we remove self-ref cap at slot 0
    // @billn: but why??
    seL4_Error error = seL4_Untyped_Retype(shadow_cnode_cslot_to_cptr(shadow_cnode, ut_cslot), object_type, size_bits,
                                           shadow_cnode->cnode_cptr, 0, 0, destination_cslot, 1);
    if (error != seL4_NoError) {
        LOG_ERR("failed to UT retype object type %lu, UT CPtr: 0x%lx, size_bits: %hhu, error: %d\n", object_type,
                shadow_cnode->cnode_cptr + ut_cslot, size_bits, error);
        return false;
    }

    shadow_cap_type_t cap_type = sel4_obj_type_to_shadow_cap_type(object_type);
    assert(cap_type);
    shadow_cap_t new_cap = SHADOW_CNODE_MAKE_CAP(cap_type, start, end, ut_cslot, 0);
    if (cap_type == CAP_TYPE_UT) {
        new_cap.as_ut.watermark = start;
        new_cap.as_ut.is_device = ut->as_ut.is_device;
    }

    assert(shadow_cnode_insert_cap_at_slot(shadow_cnode, &new_cap, destination_cslot));

    ut->as_ut.watermark = end;
    if (retyped_cslot) {
        *retyped_cslot = destination_cslot;
    }
    return true;
}

bool shadow_cnode_retype_at_paddr(shadow_cnode_t *shadow_cnode, seL4_Word target_paddr, seL4_Word object_type,
                                  seL4_Word size_bits, size_t *retyped_cslot)
{
    uint8_t obj_bits = get_object_size_bits(object_type, size_bits);
    if (obj_bits == 0) {
        LOG_ERR("bad object type %lu or size_bits %lu\n", object_type, size_bits);
        return false;
    }
    if (target_paddr & (BIT(obj_bits) - 1)) {
        LOG_ERR("paddr 0x%lx not aligned to object size\n", target_paddr);
        return false;
    }

    size_t candidate_ut_cslot;
    if (!get_untyped_containing_paddr(shadow_cnode, target_paddr, &candidate_ut_cslot)) {
        return false;
    }

    shadow_cap_t *ut = &shadow_cnode->caps[candidate_ut_cslot];
    if (target_paddr + BIT(obj_bits) > ut->end_paddr) {
        LOG_ERR("object at paddr 0x%lx overruns untyped %lu: 0x%lx..0x%lx\n", target_paddr, candidate_ut_cslot,
                ut->base_paddr, ut->end_paddr);
        return false;
    }

    /* Fill [watermark, target) with child untypeds so the object lands exactly at target.
     * The children stay in the CNode and can be used later. */
    while (ut->as_ut.watermark < target_paddr) {
        uint64_t wm = ut->as_ut.watermark;
        int align_bits = wm ? __builtin_ctzll(wm) : 63;
        int gap_bits = 63 - __builtin_clzll(target_paddr - wm);
        if (!untyped_retype(shadow_cnode, candidate_ut_cslot, seL4_UntypedObject, MIN(align_bits, gap_bits), NULL)) {
            return false;
        }
    }

    /* Lets make sure that the caller always leave the watermark at the right place.
     * Because if the watermark is not aligned by the object size, the kernel will round up! */
    assert(ut->as_ut.watermark == target_paddr);

    bool success = untyped_retype(shadow_cnode, candidate_ut_cslot, object_type, obj_bits, retyped_cslot);
    if (success && (object_type == seL4_X86_4K || object_type == seL4_X86_LargePageObject)) {
        seL4_X86_Page_GetAddress_t result = seL4_X86_Page_GetAddress(
            shadow_cnode_cslot_to_cptr(shadow_cnode, *retyped_cslot));
        assert(result.error == seL4_NoError);
        assert(result.paddr == target_paddr);
    }
    return success;
}

bool shadow_cnode_retype(shadow_cnode_t *shadow_cnode, seL4_Word object_type, seL4_Word size_bits,
                         size_t *retyped_cslot)
{
    uint8_t obj_bits = get_object_size_bits(object_type, size_bits);
    if (obj_bits == 0) {
        LOG_ERR("bad object type %lu or size_bits %lu\n", object_type, size_bits);
        return false;
    }

    size_t candidate_ut_cslot = 0;
    for (; candidate_ut_cslot < shadow_cnode->num_slots; candidate_ut_cslot++) {
        /* @billn: could be further improved by considering the UT that will
         * cause the kernel to round up the least. */
        if (shadow_cnode->caps[candidate_ut_cslot].type == CAP_TYPE_UT) {
            shadow_cap_t *ut = &shadow_cnode->caps[candidate_ut_cslot];
            if (!ut->as_ut.is_device) {
                uint64_t base = ROUND_UP(ut->as_ut.watermark, BIT(obj_bits));
                uint64_t end = base + BIT(obj_bits);

                if (end <= ut->end_paddr) {
                    break;
                }
            }
        }
    }
    if (candidate_ut_cslot == shadow_cnode->num_slots) {
        LOG_ERR("can't find a non-device UT that fits\n");
        return false;
    }

    return untyped_retype(shadow_cnode, candidate_ut_cslot, object_type, obj_bits, retyped_cslot);
}

// // seL4_Error pass_ut_with_range(cnode_specs_t *dst_cnode_specs,
// //                               cnode_specs_t *src_cnode_specs,
// //                               uintptr_t min_addr,
// //                               uintptr_t max_addr)
// // {
// //     if (min_addr >= max_addr) {
// //         return seL4_NoError;
// //     }

// //     uint32_t target_ut_idx;
// //     seL4_Error error = get_untyped_at_paddr(src_cnode_specs, min_addr, &target_ut_idx);
// //     if (error != seL4_NoError) {
// //         sddf_dprintf("Error: failed to found the untyped containing physical address: 0x%lx\n", min_addr);
// //         return error;
// //     }

// //     seL4_Word max_align_size_bits = 0;
// //     while (max_align_size_bits < 64) {
// //         uint8_t offset_bit = (src_cnode_specs->caps[target_ut_idx].base_addr >> max_align_size_bits) & 0x1;
// //         if (offset_bit) break;
// //         max_align_size_bits += 1;
// //     }
// //     /* seL4_Word max_align_size = (1ULL << max_align_size_bits); */

// //     seL4_Word avai_mem_size = src_cnode_specs->caps[target_ut_idx].end_addr - min_addr;
// //     seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);
// //     seL4_Word max_target_size_bits = max_size_bits(max_addr - min_addr);
// //     seL4_Word new_ut_size_bits = MIN(MIN(avai_mem_size_bits, max_target_size_bits), max_align_size_bits);
// //     seL4_Word new_ut_size = (1ULL << new_ut_size_bits);

// //     uint32_t retyped_cptr_idx;
// //     /* sddf_dprintf("Try passing the ut min_addr: 0x%lx, max_addr: 0x%lx\n", min_addr, max_addr); */
// //     error = untyped_retype(src_cnode_specs, target_ut_idx, seL4_UntypedObject, new_ut_size_bits, &retyped_cptr_idx);
// //     if (error != seL4_NoError) {
// //         sddf_dprintf("Error: failed to retype an untyped [0x%lx-0x%lx] from an untyped(%d)[0x%lx-0x%lx]\n",
// //                      min_addr,
// //                      min_addr + new_ut_size,
// //                      target_ut_idx,
// //                      src_cnode_specs->caps[target_ut_idx].base_addr,
// //                      src_cnode_specs->caps[target_ut_idx].end_addr);
// //         return error;
// //     }

// //     // TODO: remove hardcoded value
// //     // depth = guardSize + radixSize = 50 + 8 for CNode 'remaining_untypeds'
// //     error = seL4_CNode_Copy(dst_cnode_specs->cptr, dst_cnode_specs->end, 58, src_cnode_specs->cptr, retyped_cptr_idx, 58, seL4_ReadWrite);
// //     if (error != seL4_NoError) {
// //         sddf_dprintf("Error: failed to copy a capability\n");
// //         return error;
// //     }
// //     /* sddf_dprintf("pass ut to slot %d in destination CNode from slot %d in src\n", dst_cnode_specs->end, target_ut_idx); */

// //     dst_cnode_specs->caps[dst_cnode_specs->end].base_addr = min_addr;
// //     dst_cnode_specs->caps[dst_cnode_specs->end].end_addr = min_addr + new_ut_size;
// //     dst_cnode_specs->end++;

// //     if (min_addr + new_ut_size < max_addr) {
// //         pass_ut_with_range(dst_cnode_specs, src_cnode_specs, min_addr + new_ut_size, max_addr);
// //     }
// //     return seL4_NoError;
// // }

// void clear_cnode_specs_entry(cnode_specs_t *cnode_specs, uint32_t ut_idx)
// {
//     cnode_specs->caps[ut_idx].base_addr = 0;
//     cnode_specs->caps[ut_idx].end_addr = 0;
//     cnode_specs->caps[ut_idx].is_device = 0;
//     cnode_specs->caps[ut_idx].object_type = 0;
//     cnode_specs->caps[ut_idx].parent = 0;
//     cnode_specs->caps[ut_idx].child = 0;
// }

// bool update_cnode_specs_after_revoke(cnode_specs_t *cnode_specs,
//                                      uint32_t ut_idx)
// {
//     if (cnode_specs->caps[ut_idx].child) {
//         uint32_t child_ut_idx = cnode_specs->caps[ut_idx].child;
//         uintptr_t base_addr = 0;
//         uintptr_t end_addr = 0;
//         while (child_ut_idx != 0) {
//             bool success = update_cnode_specs_after_revoke(cnode_specs, child_ut_idx);
//             if (!success) {
//                 return success;
//             }
//             if (base_addr == end_addr) {
//                 base_addr = cnode_specs->caps[child_ut_idx].base_addr;
//                 end_addr = cnode_specs->caps[child_ut_idx].end_addr;
//                 clear_cnode_specs_entry(cnode_specs, child_ut_idx);
//             } else if (end_addr == cnode_specs->caps[child_ut_idx].base_addr) {
//                 end_addr = cnode_specs->caps[child_ut_idx].end_addr;
//                 clear_cnode_specs_entry(cnode_specs, child_ut_idx);
//             } else {
//                 sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
//                 return false;
//             }

//             uint32_t child_cleared_idx = child_ut_idx;
//             child_ut_idx = cnode_specs->caps[child_ut_idx].next;
//             cnode_specs->caps[child_cleared_idx].next = 0;
//         }

//         if (end_addr != cnode_specs->caps[ut_idx].base_addr) {
//             sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
//             return false;
//         }
//         cnode_specs->caps[ut_idx].base_addr = base_addr;
//         cnode_specs->caps[ut_idx].child = 0;
//     }
//     return true;
// }

// void update_active_ut_idx(cnode_specs_t *cnode_specs)
// {
//     // TODO: find a proper untyped for PT objects, not the first one is used by capDL initialiser
//     uint32_t non_dev_mem_id = 0;
//     uint32_t i;
//     for (i = cnode_specs->start; i < cnode_specs->end; i++) {
//         if (cnode_specs->caps[i].is_device == false && cnode_specs->caps[i].object_type == seL4_UntypedObject) {
//             if (non_dev_mem_id == 5) {
//                 cnode_specs->active_ut_idx = i;
//                 break;
//             }
//             non_dev_mem_id++;
//         }
//     }
//     if (i < cnode_specs->end) {
//         sddf_dprintf("Found an untyped for kernel objects: ut idx: 0x%x, paddr: 0x%lx\n", cnode_specs->active_ut_idx, cnode_specs->caps[i].base_addr);
//     } else {
//         sddf_dprintf("[Error] failed to find an available untyped for kernel objects allocation\n");
//     }
// }

// // DANGER: can destroy objects created by capDL initialiser!
// // seL4_Error cnode_untypeds_revoke(cnode_specs_t *cnode_specs)
// // {
// //     for (uint32_t i = cnode_specs->end - 1; i >= cnode_specs->start; i--) {
// //         uint32_t parent_ut_idx = i;
// //         while (cnode_specs->caps[parent_ut_idx].parent) {
// //             parent_ut_idx = cnode_specs->caps[parent_ut_idx].parent;
// //         }

// //         // Revoke if this cap has been divided into small ones
// //         if (parent_ut_idx != i) {
// //             // TODO: proper way to calculate `depth`
// //             seL4_Error error = seL4_CNode_Revoke(cnode_specs->cptr, parent_ut_idx, 58);
// //             if (error != seL4_NoError) {
// //                 return error;
// //             }

// //             bool success = update_cnode_specs_after_revoke(cnode_specs, parent_ut_idx);
// //             if (!success) {
// //                 return seL4_IllegalOperation;
// //             }
// //         }

// //         if (cnode_specs->caps[i].end_addr == 0) {
// //             cnode_specs->end = i;
// //         }
// //     }

// //     return seL4_NoError;
// // }
