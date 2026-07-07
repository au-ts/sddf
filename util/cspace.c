#include "cspace.h"


seL4_Word max_size_bits(seL4_Word size)
{
    seL4_Word i = 63;
    while (((1ULL << i) & size) == 0) {
        i--;
    }
    return i;
}


seL4_Error pass_ut_with_range(uintptr_t min_addr, uintptr_t max_addr)
{
    uint32_t target_ut_idx;
    seL4_Error error = get_untyped_at_paddr(min_addr, &target_ut_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to found the untyped containing physical address: 0x%lx\n", min_addr);
        return error;
    }

    seL4_Word avai_mem_size = cap_list[target_ut_idx].end_addr - min_addr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);
    seL4_Word max_target_size_bits = max_size_bits(max_addr - min_addr);
    seL4_Word new_ut_size_bits = MIN(avai_mem_size_bits, max_target_size_bits);
    seL4_Word new_ut_size = (1ULL << new_ut_size_bits);

    uint32_t retyped_cptr_idx;
    /* sddf_dprintf("min_addr: 0x%lx, max_addr: 0x%lx\n", min_addr, max_addr); */
    error = untyped_retype(target_ut_idx, seL4_UntypedObject, new_ut_size_bits, &retyped_cptr_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype an untyped [0x%lx-0x%lx] from an untyped(%d)[0x%lx-0x%lx]\n",
                     min_addr,
                     max_addr,
                     retyped_cptr_idx,
                     cap_list[retyped_cptr_idx].base_addr,
                     cap_list[retyped_cptr_idx].end_addr);
        return error;
    }

    // depth = guardSize + radixSize = 50 + 8 for CNode 'remaining_untypeds'
    error = seL4_CNode_Copy(cnode_cptr_pci_resources, cnode_pci_resources_free_slot, 58, cnode_cptr_remaining_untypeds, retyped_cptr_idx, 58, seL4_ReadWrite);
    /* error = seL4_CNode_Move(cnode_cptr_pci_resources, cnode_pci_resources_free_slot, 58, cnode_cptr_remaining_untypeds, retyped_cptr_idx, 58); */
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to copy a capability\n");
        return error;
    }
    /* sddf_dprintf("copy ut to slot %lu, start: %u, end: %u\n", cnode_pci_resources_free_slot, cnode_caps_pci_resources->start, cnode_caps_pci_resources->end); */

    cnode_caps_pci_resources->desc[cnode_caps_pci_resources->end].base_addr = min_addr;
    cnode_caps_pci_resources->desc[cnode_caps_pci_resources->end].end_addr = min_addr + new_ut_size;
    cnode_caps_pci_resources->end++;
    cnode_pci_resources_free_slot++;

    if (min_addr + new_ut_size < max_addr) {
        pass_ut_with_range(min_addr + new_ut_size, max_addr);
    }
    return seL4_NoError;
}


seL4_Error untyped_retype(uint32_t ut_idx,
                          seL4_Word object_type,
                          seL4_Word size_bits,
                          uint32_t *retyped_cptr_idx)
{
    seL4_Error error = seL4_Untyped_Retype(cnode_cptr_remaining_untypeds + ut_idx,
                                object_type,
                                size_bits,
                                cnode_cptr_remaining_untypeds, 0, 0,
                                cap_list_end, 1);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype an object type %lu, size_bits: %lu - error: %d\n", object_type, size_bits, error);
        return error;
    }

    /* sddf_dprintf("Retyped object type %lu, size_bits=%lu at 0x%lx to destination %d\n", object_type, size_bits, cap_list[ut_idx].base_addr, cap_list_end); */

    cap_list[cap_list_end].base_addr = cap_list[ut_idx].base_addr;
    cap_list[cap_list_end].end_addr = cap_list[ut_idx].base_addr + (1ULL << get_object_size(object_type, size_bits));
    cap_list[cap_list_end].object_type = object_type;
    cap_list[cap_list_end].object_type = cap_list[ut_idx].is_device;
    cap_list[cap_list_end].parent = ut_idx;
    cap_list[cap_list_end].child = 0;
    cap_list[cap_list_end].next = 0;
    cap_list[ut_idx].base_addr = cap_list[cap_list_end].end_addr;

    if (cap_list[ut_idx].child == 0) {
        cap_list[ut_idx].child = cap_list_end;
    } else {
        uint32_t child_ut_idx = cap_list[ut_idx].child;

        while (cap_list[child_ut_idx].next != 0) {
            child_ut_idx = cap_list[child_ut_idx].next;
        }
        cap_list[child_ut_idx].next = cap_list_end;
    }

    if (retyped_cptr_idx != NULL) {
        *retyped_cptr_idx = cap_list_end;
    }
    cap_list_end++;

    return seL4_NoError;
}

seL4_Error retype_at_paddr(seL4_Word target_paddr,
                           seL4_Word object_type,
                           seL4_Word size_bits,
                           uint32_t *retyped_cptr_idx)
{
    uint32_t target_ut_idx;
    seL4_Error error = get_untyped_at_paddr(target_paddr, &target_ut_idx);
    if (error != seL4_NoError) {
        return error;
    }

    seL4_Word avai_mem_size = cap_list[target_ut_idx].end_addr - target_paddr;
    seL4_Word avai_mem_size_bits = max_size_bits(avai_mem_size);

    if (object_type != seL4_UntypedObject && avai_mem_size_bits < size_bits) {
        sddf_dprintf("Error: Untyped(%d)[0x%lx-0x%lx] has insufficient memory for (paddr: 0x%lx, size_bits: %lu)\n",
                     target_ut_idx,
                     cap_list[target_ut_idx].base_addr,
                     cap_list[target_ut_idx].end_addr,
                     target_paddr,
                     size_bits);
        return 0;
    }

    // Retype the target object
    return untyped_retype(target_ut_idx, object_type, size_bits, retyped_cptr_idx);
}

void clear_cap_list_entry(uint32_t ut_idx)
{
    cap_list[ut_idx].base_addr = 0;
    cap_list[ut_idx].end_addr = 0;
    cap_list[ut_idx].is_device = 0;
    cap_list[ut_idx].object_type = 0;
    cap_list[ut_idx].parent = 0;
    cap_list[ut_idx].child = 0;
}

bool update_cap_list_after_revoke(uint32_t ut_idx)
{
    if (cap_list[ut_idx].child) {
        uint32_t child_ut_idx = cap_list[ut_idx].child;
        uintptr_t base_addr = 0;
        uintptr_t end_addr = 0;
        while (child_ut_idx != 0) {
            bool success = update_cap_list_after_revoke(child_ut_idx);
            if (!success) {
                return success;
            }
            if (base_addr == end_addr) {
                base_addr = cap_list[child_ut_idx].base_addr;
                end_addr = cap_list[child_ut_idx].end_addr;
                clear_cap_list_entry(child_ut_idx);
            } else if (end_addr == cap_list[child_ut_idx].base_addr) {
                end_addr = cap_list[child_ut_idx].end_addr;
                clear_cap_list_entry(child_ut_idx);
            } else {
                sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
                return false;
            }

            uint32_t child_cleared_idx = child_ut_idx;
            child_ut_idx = cap_list[child_ut_idx].next;
            cap_list[child_cleared_idx].next = 0;
        }

        if (end_addr != cap_list[ut_idx].base_addr) {
            sddf_dprintf("Error: something wrong during re-collecting untypeds\n");
            return false;
        }
        cap_list[ut_idx].base_addr = base_addr;
        cap_list[ut_idx].child = 0;
    }
    return true;
}


seL4_Error get_untyped_at_paddr(seL4_Word target_paddr,
                                uint32_t *target_ut_idx)
{
    uint32_t ut_idx = cap_list_end;
    for (uint32_t i = cap_list_start; i < cap_list_end; i++) {
        if (cap_list[i].base_addr <= target_paddr && target_paddr < cap_list[i].end_addr && cap_list[i].object_type == seL4_UntypedObject) {
            ut_idx = i;
            break;
        }
    }
    if (ut_idx == cap_list_end) {
        sddf_dprintf("Error: Untyped containing physical address 0x%lx is not found\n", target_paddr);
        return seL4_InvalidArgument;
    }
    /* sddf_dprintf("Found the untyped containing physical address: 0x%lx\n", target_paddr); */
    /* sddf_dprintf("ut idx: %u, base_addr: 0x%lx, end_addr: 0x%lx\n", ut_idx, cap_list[ut_idx].base_addr, cap_list[ut_idx].end_addr); */

    seL4_Error error;

    // Divide untyped to smaller ones
    // TODO: figure out what's the maxinum and minimum bits here
    for (int bits = 63; bits >= 12; bits--) {
        while (target_paddr - cap_list[ut_idx].base_addr >= (1ULL << bits)) {
            error = untyped_retype(ut_idx, seL4_UntypedObject, bits, NULL);
            if (error != seL4_NoError){
                sddf_dprintf("Error: failed to divide an untyped(%d)[0x%lx-0x%lx] to a smaller untyped with size_bits=%d\n",
                             ut_idx,
                             cap_list[ut_idx].base_addr,
                             cap_list[ut_idx].end_addr,
                             bits);
                return error;
            }
        }
    }

    *target_ut_idx = ut_idx;
    return seL4_NoError;
}

void update_active_ut_idx(cnode_specs_t cnode_specs)
{
    // TODO: find a proper untyped for PT objects, not the first one is used by capDL initialiser
    uint32_t non_dev_mem_id = 0;
    for (uint32_t i = cnode_specs.start; i < cnode_specs.end; i++) {
        if (cnode_specs.caps[i].is_device == false && cnode_specs.caps[i].object_type == seL4_UntypedObject) {
            if (non_dev_mem_id == 5) {
                cnode_specs.active_ut_idx = i;
                break;
            }
            non_dev_mem_id++;
        }
    }
    if (i < cnode_specs.end) {
        sddf_dprintf("Found an untyped for kernel objects: ut idx: 0x%x, paddr: 0x%lx\n", kernel_objects_ut_idx, cap_list[kernel_objects_ut_idx].base_addr);
    } else {
        sddf_dprintf("[Error] failed to find an available untyped for kernel objects allocation\n");
    }
}

seL4_Error untypeds_revoke(cnode_specs_t cnode_specs)
{
    for (uint32_t i = cnode_specs.end - 1; i >= cnode_specs.start; i--) {
        uint32_t parent_ut_idx = i;
        while (cnode_specs.caps[parent_ut_idx].parent) {
            parent_ut_idx = cnode_specs.caps[parent_ut_idx].parent;
        }

        // Revoke if this cap has been divided into small ones
        if (parent_ut_idx != i) {
            // TODO: proper way to calculate `depth`
            seL4_Error error = seL4_CNode_Revoke(cnode_specs.cptr, parent_ut_idx, 58);
            if (error != seL4_NoError) {
                return error;
            }

            bool success = update_cap_list_after_revoke(parent_ut_idx);
            if (!success) {
                return seL4_IllegalOperation;
            }
        }

        if (cap_list[i].end_addr == 0) {
            cap_list_end = i;
        }
    }

    return seL4_NoError;
}
