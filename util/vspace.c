#include <microkit.h>
#include <sddf/util/util.h>
#include <sddf/util/vspace.h>
#include <sddf/util/printf.h>
#include <sel4/sel4_arch/mapping.h>

// #define CONFIG_DEBUG_VSPACE

#if defined(CONFIG_DEBUG_VSPACE)
#define LOG_VSPACE(fmt, ...) \
    sddf_dprintf("VSPACE UTIL %s:%d|INFO: " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
#define LOG_VSPACE(fmt, ...) do {} while (0)
#endif

#define LOG_ERR(fmt, ...) \
    sddf_dprintf("VSPACE UTIL %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)

#define SMALL_PAGE_OFFSET(addr) ((addr) & (BIT(seL4_PageBits) - 1))
#define SMALL_PAGE_SIZE BIT(seL4_PageBits)

static bool map_frame(shadow_cnode_t *shadow_cnode, seL4_CPtr vspace_cptr, seL4_CPtr frame_cptr, uintptr_t vaddr,
                      seL4_CapRights_t rights, seL4_X86_VMAttributes vm_attr)
{
    seL4_Error err = seL4_X86_Page_Map(frame_cptr, vspace_cptr, vaddr, rights, vm_attr);
    if (err == seL4_NoError) {
        LOG_VSPACE("mapped at vaddr 0x%lx\n", vaddr);
        return true;
    }

    for (int i = 0; i < 4 && err == seL4_FailedLookup; i++) {
        seL4_Word failed = seL4_MappingFailedLookupLevel();
        size_t retyped_cslot;

        switch (failed) {
        case SEL4_MAPPING_LOOKUP_NO_PT: {
            if (!shadow_cnode_retype(shadow_cnode, seL4_X86_PageTableObject, 0, &retyped_cslot)) {
                LOG_ERR("Can't create last level paging object\n");
                return false;
            }
            err = seL4_X86_PageTable_Map(shadow_cnode_cslot_to_cptr(shadow_cnode, retyped_cslot), vspace_cptr, vaddr,
                                         seL4_X86_Default_VMAttributes);
            if (err != seL4_NoError) {
                LOG_ERR("Can't map last level paging object\n");
                return false;
            }
            break;
        }
        case SEL4_MAPPING_LOOKUP_NO_PD: {
            if (!shadow_cnode_retype(shadow_cnode, seL4_X86_PageDirectoryObject, 0, &retyped_cslot)) {
                LOG_ERR("Can't create second-last level paging object\n");
                return false;
            }
            err = seL4_X86_PageDirectory_Map(shadow_cnode_cslot_to_cptr(shadow_cnode, retyped_cslot), vspace_cptr,
                                             vaddr, seL4_X86_Default_VMAttributes);
            if (err != seL4_NoError) {
                LOG_ERR("Can't map second-last level paging object\n");
                return false;
            }
            break;
        }
        case SEL4_MAPPING_LOOKUP_NO_PDPT: {
            if (!shadow_cnode_retype(shadow_cnode, seL4_X86_PDPTObject, 0, &retyped_cslot)) {
                LOG_ERR("Can't create third-last level paging object\n");
                return false;
            }
            err = seL4_X86_PDPT_Map(shadow_cnode_cslot_to_cptr(shadow_cnode, retyped_cslot), vspace_cptr, vaddr,
                                    seL4_X86_Default_VMAttributes);
            if (err != seL4_NoError) {
                LOG_ERR("Can't map third-last level paging object\n");
                return false;
            }
            break;
        }
        }

        err = seL4_X86_Page_Map(frame_cptr, vspace_cptr, vaddr, rights, vm_attr);
        if (err == seL4_NoError) {
            LOG_VSPACE("mapped at vaddr 0x%lx\n", vaddr);
            return true;
        }
    }

    return false;
}

static bool retype_and_map_frame(shadow_cnode_t *shadow_cnode, seL4_CPtr vspace_cptr, uintptr_t paddr, uintptr_t vaddr,
                                 seL4_CapRights_t rights, seL4_X86_VMAttributes vm_attr)
{
    size_t retyped_cslot;
    if (!shadow_cnode_retype_at_paddr(shadow_cnode, paddr, seL4_X86_4K, seL4_PageBits, &retyped_cslot)) {
        LOG_ERR("failed to retype at paddr 0x%lx\n", paddr);
        return false;
    }

    if (!map_frame(shadow_cnode, vspace_cptr, shadow_cnode_cslot_to_cptr(shadow_cnode, retyped_cslot), vaddr, rights,
                   vm_attr)) {
        LOG_ERR("failed to map frame at vaddr: 0x%lx\n", vaddr);
        return false;
    }

    return true;
}

bool map_memory_region(shadow_cnode_t *shadow_cnode, seL4_CPtr vspace_cptr, uintptr_t paddr, size_t size,
                       uintptr_t vaddr, seL4_CapRights_t rights, seL4_X86_VMAttributes vm_attr)
{
    if (SMALL_PAGE_OFFSET(paddr)) {
        LOG_ERR("paddr 0x%lx must be small page aligned\n", paddr);
        return false;
    }
    if (SMALL_PAGE_OFFSET(vaddr)) {
        LOG_ERR("vaddr 0x%lx must be small page aligned\n", vaddr);
        return false;
    }
    if (!size || SMALL_PAGE_OFFSET(size)) {
        LOG_ERR("size 0x%lx must be small page aligned\n", size);
        return false;
    }
    if (!seL4_CapRights_get_capAllowRead(rights) && !seL4_CapRights_get_capAllowWrite(rights)) {
        LOG_ERR("can't have a not read and not write mapping\n");
        return false;
    }

    uint64_t curr_paddr = paddr;
    uint64_t curr_vaddr = vaddr;
    uint64_t end_paddr = paddr + size;
    while (curr_paddr < end_paddr) {
        if (!retype_and_map_frame(shadow_cnode, vspace_cptr, curr_paddr, curr_vaddr, rights, vm_attr)) {
            sddf_dprintf("Error: failed to retype or map a frame.\n");
            return false;
        }
        curr_paddr += SMALL_PAGE_SIZE;
        curr_vaddr += SMALL_PAGE_SIZE;
    }

    return true;
}
