#include "vspace.h"

#define PAGE_OFFSET(vaddr) (vaddr & 0xFFF)


seL4_Error map_frame(seL4_CPtr frame_cap, seL4_CPtr vspace, uintptr_t vaddr, seL4_CapRights_t rights)
{
    seL4_Error err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);

    for (int i = 0; i < 4 && err == seL4_FailedLookup; i++) {
        seL4_Word failed = seL4_MappingFailedLookupLevel();
        uint32_t retyped_cptr_idx;

        switch (failed) {
            case SEL4_MAPPING_LOOKUP_NO_PT: {
                err = untyped_retype(kernel_objects_ut_idx, seL4_X86_PageTableObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PageTable_Map(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
            case SEL4_MAPPING_LOOKUP_NO_PD: {
                err = untyped_retype(kernel_objects_ut_idx, seL4_X86_PageDirectoryObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PageDirectory_Map(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
            case SEL4_MAPPING_LOOKUP_NO_PDPT: {
                err = untyped_retype(kernel_objects_ut_idx, seL4_X86_PDPTObject, 0, &retyped_cptr_idx);
                if (err != seL4_NoError) {
                    return err;
                }
                err = seL4_X86_PDPT_Map(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, seL4_X86_Default_VMAttributes);
                break;
            }
        }

        if (err == seL4_NoError) {
            err = seL4_X86_Page_Map(frame_cap, vspace, vaddr, rights, seL4_X86_Default_VMAttributes);
        }
    }

    return err;
}


seL4_Error retype_and_map_frame(uintptr_t paddr, uintptr_t vaddr, seL4_CPtr vspace, seL4_Word page_type, seL4_CapRights_t rights)
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
    seL4_Error error = retype_at_paddr(paddr, page_type, 0, &retyped_cptr_idx);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to retype at paddr 0x%lx\n", paddr);
        return error;
    }

    /* sddf_dprintf("retyped and try mapping at vaddr: 0x%lx with ut idx: %u, 0x%lx\n", vaddr, retyped_cptr_idx, IDX_TO_CPTR(retyped_cptr_idx)); */
    error = map_frame(IDX_TO_CPTR(retyped_cptr_idx), vspace, vaddr, rights);
    if (error != seL4_NoError) {
        sddf_dprintf("Error: failed to map frame at vaddr: 0x%lx, err - %u\n", vaddr, error);
        return error;
    }

    return seL4_NoError;
}


// TODO: add permissions
bool map_memory_region(uintptr_t paddr, uintptr_t size, uintptr_t vaddr)
{
    assert(PAGE_OFFSET(paddr) == 0);
    assert(PAGE_OFFSET(vaddr) == 0);

    uintptr_t mapped_size = 0;
    uintptr_t mapped_paddr = ROUND_DOWN(paddr, PAGE_SIZE);
    uintptr_t end_paddr = paddr + size;
    while (paddr + mapped_size < end_paddr) {
        error = retype_and_map_frame(paddr, vaddr + mapped_size, seL4_CapInitThreadVSpace, seL4_X86_4K, seL4_CanRead);
        if (error != seL4_NoError) {
            sddf_dprintf("Error: failed to retype or map a frame.\n");
            return false;
        }
    }

    return true;
}
