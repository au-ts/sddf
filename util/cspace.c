
#pragma once
#include <sddf/util/cspace.h>
#include <sddf/util/printf.h>

seL4_Word max_size_bits(seL4_Word size)
{
    seL4_Word i = 63;
    while (((1ULL << i) & size) == 0) {
        i--;
    }
    return i;
}

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

seL4_Error get_untyped_at_paddr(cnode_specs_t *cnode_specs,
                                seL4_Word target_paddr,
                                uint32_t *target_ut_idx)
{
    uint32_t ut_idx = cnode_specs->end;
    for (uint32_t i = cnode_specs->start; i < cnode_specs->end; i++) {
        if (cnode_specs->caps[i].base_addr <= target_paddr &&
            target_paddr < cnode_specs->caps[i].end_addr &&
            cnode_specs->caps[i].object_type == seL4_UntypedObject) {
            ut_idx = i;
            break;
        }
    }
    if (ut_idx == cnode_specs->end) {
        sddf_dprintf("Error: Untyped containing physical address 0x%lx is not found\n", target_paddr);
        return seL4_InvalidArgument;
    }
    /* sddf_dprintf("Found the untyped containing physical address: 0x%lx\n", target_paddr); */
    /* sddf_dprintf("ut idx: %u, base_addr: 0x%lx, end_addr: 0x%lx\n", ut_idx, cnode_specs->caps[ut_idx].base_addr, cnode_specs->caps[ut_idx].end_addr); */

    seL4_Error error;

    // Divide untyped to smaller ones
    // TODO: figure out what's the maxinum and minimum bits here
    for (int bits = 63; bits >= 12; bits--) {
        while (target_paddr - cnode_specs->caps[ut_idx].base_addr >= (1ULL << bits)) {
            error = untyped_retype(cnode_specs, ut_idx, seL4_UntypedObject, bits, NULL);
            if (error != seL4_NoError){
                sddf_dprintf("Error: failed to divide an untyped(%d)[0x%lx-0x%lx] to a smaller untyped with size_bits=%d\n",
                             ut_idx,
                             cnode_specs->caps[ut_idx].base_addr,
                             cnode_specs->caps[ut_idx].end_addr,
                             bits);
                return error;
            }
        }
    }

    *target_ut_idx = ut_idx;
    return seL4_NoError;
}

seL4_Error pass_ut_with_range(cnode_specs_t *dst_cnode_specs,
                              cnode_specs_t *src_cnode_specs,
                              uintptr_t min_addr,
                              uintptr_t max_addr)
{
    if (min_addr >= max_addr) {
        return seL4_NoError;
    }

    uint32_t target_ut_idx;
    seL4_Error error = get_untyped_at_paddr(src_cnode_specs, min_addr, &target_ut_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to found the untyped containing physical address: 0x%lx\n", min_addr);
        return error;
    }

    seL4_Word max_align_size_bits = 0;
    while (max_align_size_bits < 64) {
        uint8_t offset_bit = (src_cnode_specs->caps[target_ut_idx].base_addr >> max_align_size_bits) & 0x1;
        if (offset_bit) break;
        max_align_size_bits += 1;
    }
    seL4_Word max_align_size = (1ULL << max_align_size_bits);

    seL4_Word avai_mem_size = src_cnode_specs->caps[target_ut_idx].end_addr - min_addr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);
    seL4_Word max_target_size_bits = max_size_bits(max_addr - min_addr);
    seL4_Word new_ut_size_bits = MIN(MIN(avai_mem_size_bits, max_target_size_bits), max_align_size_bits);
    seL4_Word new_ut_size = (1ULL << new_ut_size_bits);

    uint32_t retyped_cptr_idx;
    /* sddf_dprintf("Try passing the ut min_addr: 0x%lx, max_addr: 0x%lx\n", min_addr, max_addr); */
    error = untyped_retype(src_cnode_specs, target_ut_idx, seL4_UntypedObject, new_ut_size_bits, &retyped_cptr_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype an untyped [0x%lx-0x%lx] from an untyped(%d)[0x%lx-0x%lx]\n",
                     min_addr,
                     min_addr + new_ut_size,
                     target_ut_idx,
                     src_cnode_specs->caps[target_ut_idx].base_addr,
                     src_cnode_specs->caps[target_ut_idx].end_addr);
        return error;
    }

    // TODO: remove hardcoded value
    // depth = guardSize + radixSize = 50 + 8 for CNode 'remaining_untypeds'
    error = seL4_CNode_Copy(dst_cnode_specs->cptr, dst_cnode_specs->end, 58, src_cnode_specs->cptr, retyped_cptr_idx, 58, seL4_ReadWrite);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to copy a capability\n");
        return error;
    }
    /* sddf_dprintf("pass ut to slot %d in destination CNode from slot %d in src\n", dst_cnode_specs->end, target_ut_idx); */

    dst_cnode_specs->caps[dst_cnode_specs->end].base_addr = min_addr;
    dst_cnode_specs->caps[dst_cnode_specs->end].end_addr = min_addr + new_ut_size;
    dst_cnode_specs->end++;

    if (min_addr + new_ut_size < max_addr) {
        pass_ut_with_range(dst_cnode_specs, src_cnode_specs, min_addr + new_ut_size, max_addr);
    }
    return seL4_NoError;
}

seL4_Error untyped_retype(cnode_specs_t *cnode_specs,
                          uint32_t ut_idx,
                          seL4_Word object_type,
                          seL4_Word size_bits,
                          uint32_t *retyped_cap_idx)
{
    // @terryb: need to update this if we remove self-ref cap at slot 0
    seL4_Error error = seL4_Untyped_Retype(cnode_specs->cptr + ut_idx,
                                object_type,
                                size_bits,
                                cnode_specs->cptr, 0, 0,
                                cnode_specs->end, 1);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype an object type %lu, cptr: 0x%lx, size_bits: %lu - error: %d\n", object_type, cnode_specs->cptr + ut_idx, size_bits, error);
        return error;
    }

    cnode_specs->caps[cnode_specs->end].base_addr = cnode_specs->caps[ut_idx].base_addr;
    cnode_specs->caps[cnode_specs->end].end_addr = cnode_specs->caps[ut_idx].base_addr + GET_OBJECT_SIZE(object_type, size_bits);
    cnode_specs->caps[cnode_specs->end].object_type = object_type;
    cnode_specs->caps[cnode_specs->end].is_device = cnode_specs->caps[ut_idx].is_device;
    cnode_specs->caps[cnode_specs->end].parent = ut_idx;
    cnode_specs->caps[cnode_specs->end].child = 0;
    cnode_specs->caps[cnode_specs->end].next = 0;
    cnode_specs->caps[ut_idx].base_addr = cnode_specs->caps[cnode_specs->end].end_addr;

    if (cnode_specs->caps[ut_idx].child == 0) {
        cnode_specs->caps[ut_idx].child = cnode_specs->end;
    } else {
        uint32_t child_ut_idx = cnode_specs->caps[ut_idx].child;

        while (cnode_specs->caps[child_ut_idx].next != 0) {
            child_ut_idx = cnode_specs->caps[child_ut_idx].next;
        }
        cnode_specs->caps[child_ut_idx].next = cnode_specs->end;
    }

    if (retyped_cap_idx != NULL) {
        *retyped_cap_idx = cnode_specs->end;
    }
    cnode_specs->end++;

    return seL4_NoError;
}

seL4_Error retype_at_paddr(cnode_specs_t *cnode_specs,
                           seL4_Word target_paddr,
                           seL4_Word object_type,
                           seL4_Word size_bits,
                           uint32_t *retyped_cptr_idx)
{
    uint32_t dest_ut_idx;
    seL4_Error error = get_untyped_at_paddr(cnode_specs, target_paddr, &dest_ut_idx);
    if (error != seL4_NoError) {
        return error;
    }

    seL4_Word avai_mem_size = cnode_specs->caps[dest_ut_idx].end_addr - target_paddr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);

    if (object_type != seL4_UntypedObject && avai_mem_size_bits < size_bits) {
        sddf_dprintf("Error: Untyped(%d)[0x%lx-0x%lx] has insufficient memory for (paddr: 0x%lx, size_bits: %lu)\n",
                     dest_ut_idx,
                     cnode_specs->caps[dest_ut_idx].base_addr,
                     cnode_specs->caps[dest_ut_idx].end_addr,
                     target_paddr,
                     size_bits);
        return 0;
    }

    // Retype the target object
    return untyped_retype(cnode_specs, dest_ut_idx, object_type, size_bits, retyped_cptr_idx);
}

void clear_cnode_specs_entry(cnode_specs_t *cnode_specs, uint32_t ut_idx)
{
    cnode_specs->caps[ut_idx].base_addr = 0;
    cnode_specs->caps[ut_idx].end_addr = 0;
    cnode_specs->caps[ut_idx].is_device = 0;
    cnode_specs->caps[ut_idx].object_type = 0;
    cnode_specs->caps[ut_idx].parent = 0;
    cnode_specs->caps[ut_idx].child = 0;
}

bool update_cnode_specs_after_revoke(cnode_specs_t *cnode_specs,
                                     uint32_t ut_idx)
{
    if (cnode_specs->caps[ut_idx].child) {
        uint32_t child_ut_idx = cnode_specs->caps[ut_idx].child;
        uintptr_t base_addr = 0;
        uintptr_t end_addr = 0;
        while (child_ut_idx != 0) {
            bool success = update_cnode_specs_after_revoke(cnode_specs, child_ut_idx);
            if (!success) {
                return success;
            }
            if (base_addr == end_addr) {
                base_addr = cnode_specs->caps[child_ut_idx].base_addr;
                end_addr = cnode_specs->caps[child_ut_idx].end_addr;
                clear_cnode_specs_entry(cnode_specs, child_ut_idx);
            } else if (end_addr == cnode_specs->caps[child_ut_idx].base_addr) {
                end_addr = cnode_specs->caps[child_ut_idx].end_addr;
                clear_cnode_specs_entry(cnode_specs, child_ut_idx);
            } else {
                sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
                return false;
            }

            uint32_t child_cleared_idx = child_ut_idx;
            child_ut_idx = cnode_specs->caps[child_ut_idx].next;
            cnode_specs->caps[child_cleared_idx].next = 0;
        }

        if (end_addr != cnode_specs->caps[ut_idx].base_addr) {
            sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
            return false;
        }
        cnode_specs->caps[ut_idx].base_addr = base_addr;
        cnode_specs->caps[ut_idx].child = 0;
    }
    return true;
}

void update_active_ut_idx(cnode_specs_t *cnode_specs)
{
    // TODO: find a proper untyped for PT objects, not the first one is used by capDL initialiser
    uint32_t non_dev_mem_id = 0;
    uint32_t i;
    for (i = cnode_specs->start; i < cnode_specs->end; i++) {
        if (cnode_specs->caps[i].is_device == false && cnode_specs->caps[i].object_type == seL4_UntypedObject) {
            if (non_dev_mem_id == 5) {
                cnode_specs->active_ut_idx = i;
                break;
            }
            non_dev_mem_id++;
        }
    }
    if (i < cnode_specs->end) {
        sddf_dprintf("Found an untyped for kernel objects: ut idx: 0x%x, paddr: 0x%lx\n", cnode_specs->active_ut_idx, cnode_specs->caps[i].base_addr);
    } else {
        sddf_dprintf("[Error] failed to find an available untyped for kernel objects allocation\n");
    }
}

seL4_Error cnode_untypeds_revoke(cnode_specs_t *cnode_specs)
{
    for (uint32_t i = cnode_specs->end - 1; i >= cnode_specs->start; i--) {
        uint32_t parent_ut_idx = i;
        while (cnode_specs->caps[parent_ut_idx].parent) {
            parent_ut_idx = cnode_specs->caps[parent_ut_idx].parent;
        }

        // Revoke if this cap has been divided into small ones
        if (parent_ut_idx != i) {
            // TODO: proper way to calculate `depth`
            seL4_Error error = seL4_CNode_Revoke(cnode_specs->cptr, parent_ut_idx, 58);
            if (error != seL4_NoError) {
                return error;
            }

            bool success = update_cnode_specs_after_revoke(cnode_specs, parent_ut_idx);
            if (!success) {
                return seL4_IllegalOperation;
            }
        }

        if (cnode_specs->caps[i].end_addr == 0) {
            cnode_specs->end = i;
        }
    }

    return seL4_NoError;
}
