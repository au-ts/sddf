/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <microkit.h>

#include <sddf/acpi/lib_sddf_uacpi.h>
#include <sddf/util/printf.h>
#include <sddf/util/shadow_cnode.h>

// #define CONFIG_DEBUG_DRIVER

#if defined(CONFIG_DEBUG_DRIVER)
#define DEBUG_DRIVER(fmt, ...) \
    sddf_dprintf("ACPI DRIVER %s:%d|INFO: " fmt, __func__, __LINE__, ##__VA_ARGS__)
#else
#define DEBUG_DRIVER(fmt, ...) do {} while (0)
#endif

#define DEBUG_DRIVER_ERR(fmt, ...) \
    sddf_dprintf("ACPI DRIVER %s:%d|ERROR: " fmt, __func__, __LINE__, ##__VA_ARGS__)

typedef struct bootinfo_rsdp {
    seL4_BootInfoHeader header;
    lib_sddf_uacpi_rsdp_t content;
} __attribute__((packed)) bootinfo_rsdp_t;

#define RSDP_SIGNATURE "RSD PTR "

#define POST_CAPDL_CSLOT_IRQ_CONTROL 1
#define POST_CAPDL_CSLOT_IOPORT_CONTROL 2
#define POST_CAPDL_CSLOT_UNTYPEDS_START 3

typedef struct {
    seL4_Word irq_control;
    seL4_Word x86_ioport_control;
    seL4_SlotRegion ut_range;
    seL4_UntypedDesc ut_list[CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS];
} __attribute__((packed)) capDLBootInfo_t;

#define CPTR_POST_CAPDL_CNODE  (microkit_cspace_root_slot_to_cptr(1))
#define CPTR_SELF_VSPACE    (microkit_cspace_root_slot_to_cptr(2))
// #define CPTR_VSPACE_PCI_DRIVER    (microkit_cspace_root_slot_to_cptr(2))
// #define CPTR_PCI_RESOURCES        (microkit_cspace_root_slot_to_cptr(3))

capDLBootInfo_t *bootinfo_post_capdl;
bootinfo_rsdp_t *bootinfo_rsdp;

#define SHADOW_CNODE_SIZE_BITS 11 // from metaprogram
static shadow_cnode_t post_capdl_shadow_cnode;

static acpi_handover_t acpi_handover;

void init(void)
{
    if (bootinfo_rsdp->header.id != SEL4_BOOTINFO_HEADER_X86_ACPI_RSDP) {
        DEBUG_DRIVER_ERR("bootinfo_rsdp was not filled with RSDP table\n");
        return;
    }

    if (bootinfo_rsdp->header.len - sizeof(seL4_BootInfoHeader) != sizeof(lib_sddf_uacpi_rsdp_t)) {
        DEBUG_DRIVER_ERR("bootinfo_rsdp->header.len = %lu != %zu\n", bootinfo_rsdp->header.len,
                         sizeof(lib_sddf_uacpi_rsdp_t));
        return;
    }

    if (memcmp(&bootinfo_rsdp->content, RSDP_SIGNATURE, sizeof(RSDP_SIGNATURE) - 1) != 0) {
        DEBUG_DRIVER_ERR("Bad RSDP signature, expected %s, got %.8s\n", RSDP_SIGNATURE,
                         (char *)&bootinfo_rsdp->content);
        return;
    }

    DEBUG_DRIVER("Initialising shadow CNode with caps received from capDL initialiser.\n");
    if (!shadow_cnode_init(&post_capdl_shadow_cnode, SHADOW_CNODE_SIZE_BITS, CPTR_POST_CAPDL_CNODE)) {
        DEBUG_DRIVER_ERR("Failed to initialise shadow CNode\n");
        return;
    }

    assert(shadow_cnode_insert_cap_at_slot(&post_capdl_shadow_cnode,
                                           &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_IRQ_CONTROL, 0, 0, PARENT_CSLOT_NONE, 0),
                                           POST_CAPDL_CSLOT_IRQ_CONTROL));
    assert(shadow_cnode_insert_cap_at_slot(
        &post_capdl_shadow_cnode, &SHADOW_CNODE_MAKE_CAP(CAP_TYPE_X86_IO_PORT_CONTROL, 0, 0, PARENT_CSLOT_NONE, 0),
        POST_CAPDL_CSLOT_IOPORT_CONTROL));

    DEBUG_DRIVER("UTs received from capDL initialiser:\n");
    for (uint64_t i = bootinfo_post_capdl->ut_range.start; i < bootinfo_post_capdl->ut_range.end; i++) {
        seL4_UntypedDesc *post_capdl_ut_desc = &bootinfo_post_capdl->ut_list[i - bootinfo_post_capdl->ut_range.start];

        uint64_t base_paddr = post_capdl_ut_desc->paddr;
        uint64_t watermark = post_capdl_ut_desc->paddr;
        uint64_t end_paddr = post_capdl_ut_desc->paddr + BIT(post_capdl_ut_desc->sizeBits);
        shadow_cap_t shadow_ut_cap = SHADOW_CNODE_MAKE_CAP(CAP_TYPE_UT, base_paddr, end_paddr, PARENT_CSLOT_NONE, 0);
        shadow_ut_cap.as_ut = (shadow_ut_t) {
            .watermark = watermark,
            .is_device = post_capdl_ut_desc->isDevice,
        };

        if (!shadow_cnode_insert_cap_at_slot(&post_capdl_shadow_cnode, &shadow_ut_cap, i)) {
            DEBUG_DRIVER_ERR("Failed to bookkeep UT at idx %lu\n", i);
            return;
        }

        DEBUG_DRIVER("CSlot: 0x%lx, base: 0x%lx, end: 0x%lx, device? %d\n", i, base_paddr, end_paddr,
                     shadow_ut_cap.as_ut.is_device);
    }

    sddf_uacpi_init_args_t init_args = (sddf_uacpi_init_args_t) {
        .rsdp_blob = &bootinfo_rsdp->content,
        .post_capdl_shadow_cnode = &post_capdl_shadow_cnode,
        .vspace_cptr = CPTR_SELF_VSPACE,
    };

    if (!sddf_uacpi_init(&init_args)) {
        DEBUG_DRIVER_ERR("Failed to initialise lib_sddf_uacpi\n");
        return;
    }

    if (!sddf_uacpi_retrieve_information(&acpi_handover)) {
        DEBUG_DRIVER_ERR("Failed to retrieve ACPI information\n");
        return;
    }

    if (!sddf_uacpi_teardown()) {
        DEBUG_DRIVER_ERR("Failed to teardown lib_sddf_uacpi\n");
        return;
    }

    return;
}

void notified(microkit_channel ch)
{
}
