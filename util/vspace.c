#pragma once
#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/vspace.h>
#include <sddf/util/printf.h>
#include <sel4/sel4_arch/mapping.h>


seL4_Error map_frame(cnode_specs_t *ut_cnode_specs, seL4_CPtr frame_cap, seL4_CPtr vspace, uintptr_t vaddr, seL4_CapRights_t rights)
{
    seL4_Error err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);

    for (int i = 0; i < 4 && err == seL4_FailedLookup; i++) {
        seL4_Word failed = seL4_MappingFailedLookupLevel();
        uint32_t retyped_cptr_idx;

        switch (failed) {
            case SEL4_MAPPING_LOOKUP_NO_PT: {
                err = untyped_retype(ut_cnode_specs, ut_cnode_specs->active_ut_idx, seL4_X86_PageTableObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PageTable_Map(IDX_TO_CPTR(ut_cnode_specs, retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
            case SEL4_MAPPING_LOOKUP_NO_PD: {
                err = untyped_retype(ut_cnode_specs, ut_cnode_specs->active_ut_idx, seL4_X86_PageDirectoryObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PageDirectory_Map(IDX_TO_CPTR(ut_cnode_specs, retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
            case SEL4_MAPPING_LOOKUP_NO_PDPT: {
                err = untyped_retype(ut_cnode_specs, ut_cnode_specs->active_ut_idx, seL4_X86_PDPTObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PDPT_Map(IDX_TO_CPTR(ut_cnode_specs, retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
        }

        if (err == seL4_NoError) {
            err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);
        }
    }

    return err;
}


seL4_Error retype_and_map_frame(cnode_specs_t *cnode_specs, uintptr_t paddr, uintptr_t vaddr, seL4_CPtr vspace, seL4_Word page_type, seL4_CapRights_t rights)
{
    uint32_t retyped_cptr_idx;
    // TODO: round_down for large pages and check if it's a page type
    if (page_type == seL4_X86_4K) {
        paddr = ROUND_DOWN(paddr, 1UL << seL4_PageBits);
        vaddr = ROUND_DOWN(vaddr, 1UL << seL4_PageBits);
    } else if (page_type == seL4_X86_LargePageObject) {
        paddr = ROUND_DOWN(paddr, 1UL << seL4_LargePageBits);
        vaddr = ROUND_DOWN(vaddr, 1UL << seL4_LargePageBits);
    }
    seL4_Error error = retype_at_paddr(cnode_specs, paddr, page_type, 0, &retyped_cptr_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype at paddr 0x%lx\n", paddr);
        return error;
    }

    /* sddf_dprintf("retyped and try mapping at vaddr: 0x%lx with ut idx: %u, 0x%lx\n", vaddr, retyped_cptr_idx, IDX_TO_CPTR(retyped_cptr_idx)); */
    error = map_frame(cnode_specs, IDX_TO_CPTR(cnode_specs, retyped_cptr_idx), vspace, vaddr, rights);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to map frame at vaddr: 0x%lx, err - %u\n", vaddr, error);
        return error;
    }

    return seL4_NoError;
}


// TODO: add permissions
bool map_memory_region(cnode_specs_t *cnode_specs, uintptr_t paddr, uintptr_t size, uintptr_t vaddr)
{
    assert(PAGE_OFFSET(paddr) == PAGE_OFFSET(vaddr));

    sddf_dprintf("map 0x%lx-0x%lx to 0x%lx\n", paddr, paddr + size, vaddr);
    uintptr_t mapped_size = 0;
    uintptr_t paddr_start = ROUND_DOWN(paddr, PAGE_SIZE);
    uintptr_t vaddr_start = ROUND_DOWN(vaddr, PAGE_SIZE);
    uintptr_t end_paddr = paddr + size;
    while (paddr_start + mapped_size < end_paddr) {
        seL4_Error error = retype_and_map_frame(cnode_specs, paddr_start + mapped_size, vaddr_start + mapped_size, seL4_CapInitThreadVSpace, seL4_X86_4K, seL4_CanRead);
        if (error != seL4_NoError) {
            sddf_dprintf("Error: failed to retype or map a frame.\n");
            return false;
        }
        mapped_size += PAGE_SIZE;
    }

    return true;
}
