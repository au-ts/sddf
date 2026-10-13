/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
// #include "pci.h"

#include <stdint.h>
#include <microkit.h>
#include <sddf/acpi/handover.h>
#include <sddf/util/printf.h>
#include <sddf/util/vspace.h>

// #include <sddf/resources/device.h>
// #include <sel4/sel4_arch/mapping.h>

// pci_resources_t *pci_resources = (pci_resources_t *)0x60000000;
// cnode_specs_t *cnode_specs;
// uint32_t kernel_objects_ut_idx = 2;
// pci_bridge_node_t pci_bridge_nodes[10];
// uint32_t num_pci_bridge_nodes = 0;

// #define CPTR_CNODE_PCI_RESOURCES        (microkit_cspace_root_slot_to_cptr(1))
// #define CPTR_VSPACE_ETHERNET_DRIVER     (microkit_cspace_root_slot_to_cptr(2))
// #define CPTR_CSPACE_ETHERNET_DRIVER     (microkit_cspace_root_slot_to_cptr(3))

// bool acpi_ready = false;

// // regions[1..] are used for MSI-X BARs
// uint8_t avail_region_idx = 1;

// __attribute__((__section__(".device_resources"))) device_resources_t device_resources;
// __attribute__((__section__(".ecam_configs"))) pci_ecam_config_t pci_ecam_config;

// pci_bridge_node_t *host_bridge;
// pci_devices_config_t devices_config;

// /**
//  * Look for the capability of a device by ID
//  * */
// static struct shared_pci_cap *find_pci_cap_by_id(struct pci_header_type0 *config_space, uint8_t cap_id)
// {
//     struct shared_pci_cap *cap = (struct shared_pci_cap *)((uintptr_t)config_space + config_space->cap_ptr);
//     while (cap != (struct shared_pci_cap *)config_space) {
//         if (cap->cap_id == cap_id) {
//             return cap;
//         }
//         cap = (struct shared_pci_cap *)((uintptr_t)config_space + cap->next_ptr);
//     }
//     return NULL;
// }

// pci_bar_request_t read_bar_size(struct pci_header_type0 *pci_header, uint8_t bar_id)
// {
//     volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
//     uint32_t original_paddr_1 = (uint32_t)*mem_bar;
//     uint32_t original_paddr_2 = 0;
//     if (!(original_paddr_1 & 0x1) && (original_paddr_1 & 0x4)) {
//         original_paddr_2 = mem_bar[1];
//     }

//     *mem_bar = 0;
//     *mem_bar = 0xFFFFFFFF;
//     uint64_t readback = (uint64_t)*mem_bar;

//     uint8_t space_indicator = readback & 0x1;
//     uint8_t bar_width = (readback & 0x6) >> 1;
//     uint8_t prefetchable = (readback & 0x8) >> 3;
//     uint64_t bar_size = (~(readback | 0xFFFFFFFF00000000) | 0xF) + 1;

//     /* if (space_indicator == 0 && bar_width == 2) { */
//     /*     volatile uint64_t *mem_bar_64b = (volatile uint64_t *)mem_bar; */
//     /*     *mem_bar_64b = 0xffffffffffffffff; */
//     /*     readback = *mem_bar_64b; */
//     /*     sddf_dprintf("64bit readback: 0x%lx\n", readback); */
//     /*     bar_size = (~((uint64_t)readback) | 0xF) + 1; */
//     /* } */

//     pci_bar_request_t bar_request = {0, 0, 0, 0, 0};
//     if (readback == 0) return bar_request;

//     sddf_dprintf("BAR %u\n", bar_id);
//     sddf_dprintf("    Readback: 0x%lx\n", readback);
//     sddf_dprintf("    Original Paddr: 0x%x %x\n", original_paddr_2, original_paddr_1);
//     sddf_dprintf("    Space Indicator: %s\n", space_indicator == 1 ? "I/O" : "Memory");
//     sddf_dprintf("    Prefetchable: %s\n", prefetchable ? "true" : "false");
//     sddf_dprintf("    Width: %s\n", bar_width == 2 ? "64-bit BAR" : "32-bit BAR");

//     if (space_indicator == 1) {
//         if ((readback & 0xFFFF0000) == 0) {
//             bar_size = (~(readback | 0xFFFFFFFFFFFF0000) | 0xF) + 1;
//             bar_request.io_16bit = bar_size;
//         } else {
//             bar_request.io_32bit = bar_size;
//         }
//     } else {
//         if (prefetchable == 1 && bar_width == 2) {
//             bar_request.mem_64bit = bar_size;
//         } else if (prefetchable == 1 && bar_width == 0) {
//             bar_request.mem_32bit = bar_size;
//         } else if (prefetchable == 0) {
//             bar_request.mem_32bit_np = bar_size;
//         }
//     }
//     sddf_dprintf("    Size: 0x%lx\n", bar_size);

//     return bar_request;
// }

// bool alloc_from_resource_windows(acpi_dev_t *acpi_pci_bridge,
//                                       enum device_resource_type resource_type,
//                                       uintptr_t lower_boundary,
//                                       uintptr_t upper_boundary,
//                                       bool prefetchable,
//                                       uint64_t size,
//                                       uintptr_t *base)
// {
//     sddf_dprintf("Requested resource type 0x%x located within [0x%lx-0x%lx], prefetchable: %d, size: 0x%lx\n",
//                  resource_type,
//                  lower_boundary,
//                  upper_boundary,
//                  prefetchable,
//                  size);
//     sddf_dprintf("bridge: 0x%lx\n", (uintptr_t)acpi_pci_bridge);
//     uint8_t num_res = acpi_pci_bridge->num_dev_resources;
//     for (int j = 0; j < num_res; j++) {
//         device_resource_t *dev_res = (device_resource_t *)&acpi_pci_bridge->dev_resources[j];
//         /* sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx, type_flags: 0x%x\n", dev_res->type, dev_res->min_addr, dev_res->max_addr, dev_res->flags); */

//         if (dev_res->type != resource_type) continue;
//         if (lower_boundary > 0 && dev_res->max_addr < lower_boundary) continue;
//         if (upper_boundary > 0 && dev_res->min_addr > upper_boundary) continue;

//         // ACPI Release 6.5 Section 6.4.3.5.5 Resource Type Specific Flags
//         //   Any value set in Bits[2:1] can be treated as `prefetchable`
//         if (prefetchable && (dev_res->flags & 0x6) == 0) continue;
//         if (!prefetchable && (dev_res->flags & 0x6)) continue;

//         if (dev_res->max_addr - dev_res->min_addr < size) continue;

//         *base = (uintptr_t)dev_res->min_addr;
//         dev_res->min_addr = *base + size;
//         return true;
//     }

//     return false;
// }

// pci_resource_windows_t alloc_resource_from_host_bridge(pci_bar_request_t *req)
// {
//     uint32_t io_upper = 0x0; // Upper boundary of requested I/O end
//     if (req->io_16bit > 0) {
//         io_upper = 0x10000;
//     }
//     uint32_t io_size = (uint32_t)req->io_16bit + req->io_32bit;
//     uintptr_t io_base = 0;
//     sddf_dprintf("bridge: 0x%lx\n", (uintptr_t)host_bridge->acpi_dev);
//     if (io_size > 0 && alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_IO, 0x0, io_upper, false, io_size, &io_base)) {
//         sddf_dprintf("[Error] failed to allocate 0x%x-byte I/O from resource windows\n", io_size);
//     }

//     uint32_t mem_32bit_np_size = req->mem_32bit_np; // 32-bit non-prefetchable memory
//     uint64_t mem_p_size = req->mem_64bit; // Prefetchable memory
//     bool mem_p_is_64bit = false;
//     uintptr_t mem_p_base = 0;
//     uintptr_t mem_np_base = 0;
//     if (req->mem_32bit) {
//         // memory address must be <4GB if both 32bit and 64bit prefetchable memory is requested
//         if (alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, true, ROUND_UP(req->mem_64bit + req->mem_32bit, BIT(20)), &mem_p_base)) {
//             // Try allocating from prefetchable windows first
//             mem_p_size = ROUND_UP(req->mem_32bit + req->mem_64bit, BIT(20)); // 1MB alignment
//         } else if (alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, false, ROUND_UP(req->mem_64bit + req->mem_32bit, BIT(20)), &mem_p_base)) {
//             // Try allocating from non-prefetchable windows
//             mem_p_size = ROUND_UP(req->mem_32bit + req->mem_64bit, BIT(20)); // 1MB alignment
//         } else {
//             sddf_dprintf("[Error] failed to allocate 0x%lx bytes for prefetchable memory\n", req->mem_64bit + req->mem_32bit);
//         }
//     } else if (req->mem_32bit == 0 && req->mem_64bit > 0) {
//         if (alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_MEMORY, 0x100000000, 0x0, true, ROUND_UP(req->mem_64bit, BIT(20)), &mem_p_base)) {
//             // Try allocating from >4GB prefetchable windows first
//             mem_p_size = ROUND_UP(req->mem_64bit, BIT(20));
//         } else if (alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, true, ROUND_UP(req->mem_64bit, BIT(20)), &mem_p_base)) {
//             // Try allocating from <4GB prefetchable windows
//             mem_p_size = ROUND_UP(req->mem_64bit, BIT(20));
//         } else if (alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, false, ROUND_UP(req->mem_64bit, BIT(20)), &mem_p_base)) {
//             mem_p_size = ROUND_UP(req->mem_64bit, BIT(20));
//         } else {
//             sddf_dprintf("[Error] failed to allocate 0x%lx bytes for prefetchable memory\n", req->mem_64bit);
//         }
//     }

//     if (req->mem_32bit_np > 0) {
//         if (alloc_from_resource_windows(host_bridge->acpi_dev, ACPI_RES_TYPE_MEMORY, 0x0, 0x100000000, false, ROUND_UP(req->mem_32bit_np, BIT(20)), &mem_np_base)) {
//             mem_32bit_np_size = ROUND_UP(req->mem_32bit_np, BIT(20));
//         } else {
//             sddf_dprintf("[Error] failed to allocate 0x%lx bytes for non-prefetchable memory\n", req->mem_64bit);
//         }
//     }

//     pci_resource_windows_t allocated_windows;
//     allocated_windows.io_base = io_base;
//     allocated_windows.io_size = io_size;
//     allocated_windows.mem_np_base = mem_np_base;
//     allocated_windows.mem_np_size = mem_32bit_np_size;
//     allocated_windows.mem_p_base = mem_p_base;
//     allocated_windows.mem_p_size = mem_p_size;
//     allocated_windows.mem_p_is_64bit = mem_p_is_64bit;

//     return allocated_windows;
// }

// pci_resource_windows_t alloc_resource_from_bridge(pci_bridge_node_t *parent_bridge, pci_bar_request_t *req)
// {
//     pci_resource_windows_t *windows = &parent_bridge->windows;

//     uint32_t io_size = (uint32_t)req->io_16bit + req->io_32bit;
//     uintptr_t io_base = 0;
//     sddf_dprintf("bridge: 0x%lx\n", (uintptr_t)host_bridge->acpi_dev);
//     if (io_size > 0) {
//         if (windows->io_size >= io_size) {
//             io_base = windows->io_base;
//             windows->io_base = io_base + io_size;
//             windows->io_size -= io_size;
//         } else {
//             sddf_dprintf("[Error] failed to allocate 0x%x bytes I/O from resource windows\n", io_size);
//         }
//     }

//     uintptr_t mem_p_base = 0;
//     uintptr_t mem_np_base = 0;
//     uint32_t mem_32bit_np_size = 0;
//     uint64_t mem_p_size = 0;
//     bool mem_p_is_64bit = false;
//     if (req->mem_64bit > 0 && windows->mem_p_size >= req->mem_64bit) {
//         mem_p_base = windows->mem_p_base;
//         mem_p_size = req->mem_64bit;
//         windows->mem_p_base = mem_p_base + mem_p_size;
//         windows->mem_p_size -= mem_p_size;
//         mem_p_is_64bit = true;
//     } else if (req->mem_32bit > 0 && windows->mem_p_size >= req->mem_32bit) {
//         mem_p_base = windows->mem_p_base;
//         mem_p_size = req->mem_32bit;
//         windows->mem_p_base = mem_p_base + mem_p_size;
//         windows->mem_p_size -= mem_p_size;
//     } else {
//         mem_p_size = 0;
//         mem_32bit_np_size = req->mem_32bit + req->mem_64bit + req->mem_32bit_np;
//     }

//     if (mem_32bit_np_size > 0) {
//         if (windows->mem_np_size >= mem_32bit_np_size) {
//             mem_np_base = windows->mem_np_base;
//             windows->mem_np_base = mem_np_base + mem_32bit_np_size;
//             windows->mem_np_size -= mem_32bit_np_size;
//         } else {
//             sddf_dprintf("[Error] failed to allocate 0x%x bytes memory from resource windows\n", io_size);
//         }
//     }

//     pci_resource_windows_t allocated_windows;
//     allocated_windows.io_base = io_base;
//     allocated_windows.io_size = io_size;
//     allocated_windows.mem_np_base = mem_np_base;
//     allocated_windows.mem_np_size = mem_32bit_np_size;
//     allocated_windows.mem_p_base = mem_p_base;
//     allocated_windows.mem_p_size = mem_p_size;
//     allocated_windows.mem_p_is_64bit = mem_p_is_64bit;

//     return allocated_windows;
// }

// void map_pci_bar(pci_bridge_node_t *parent_bridge, struct pci_header_type0 *pci_header, uint8_t bar_id, uintptr_t target_vaddr, uint32_t bar_size)
// {
//     pci_bar_request_t bar_request = read_bar_size(pci_header, bar_id);
//     pci_resource_windows_t allocated_windows;

//     sddf_dprintf("  - io_16bit: 0x%x\n", bar_request.io_16bit);
//     sddf_dprintf("  - io_32bit: 0x%x\n", bar_request.io_32bit);
//     sddf_dprintf("  - mem_32bit: 0x%x\n", bar_request.mem_32bit);
//     sddf_dprintf("  - mem_64bit: 0x%lx\n", bar_request.mem_64bit);
//     sddf_dprintf("  - mem_32bit_np: 0x%x\n", bar_request.mem_32bit_np);

//     if (parent_bridge == host_bridge) {
//         allocated_windows = alloc_resource_from_host_bridge(&bar_request);
//     } else {
//         // TODO: allcoate from the parent PCI-to-PCI bridge
//         allocated_windows = alloc_resource_from_bridge(parent_bridge, &bar_request);
//     }

//     volatile uint32_t *mem_bar = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + (bar_id * 0x04));
//     bool memory_64bit = ((*mem_bar) & 0x7) == 0x4;

//     uint64_t realloc_paddr = 0;
//     if (bar_request.mem_32bit_np + bar_request.mem_32bit + bar_request.mem_64bit) {
//         if (allocated_windows.mem_p_base > 0) {
//             realloc_paddr = allocated_windows.mem_p_base;
//         } else if (allocated_windows.mem_np_base > 0) {
//             realloc_paddr = allocated_windows.mem_np_base;
//         } else {
//             sddf_dprintf("[Error] failed to allocate resource from windows\n");
//         }
//     } else {
//         sddf_dprintf("[Error] I/O BAR is not supported yet\n");
//         return;
//     }

//     sddf_dprintf("realloc_paddr: 0x%lx\n", realloc_paddr);
//     *mem_bar = realloc_paddr & 0xFFFFFFFF;
//     if (memory_64bit) {
//         volatile uint32_t *mem_bar_next = (volatile uint32_t *)((uintptr_t)pci_header + 0x10 + ((bar_id + 1) * 0x04));
//         *mem_bar_next = (realloc_paddr >> 32) & 0xFFFFFFFF;
//         sddf_dprintf("BAR uppper bits: 0x%lx\n", (realloc_paddr >> 32) & 0xFFFFFFFF);
//     }

//     sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id, *mem_bar);
//     sddf_dprintf("Memory BAR %d: 0x%x\n", bar_id + 1, mem_bar[1]);

//     seL4_Error error;
//     uintptr_t cur_paddr = realloc_paddr;
//     uintptr_t end_paddr = realloc_paddr + bar_size;
//     uintptr_t cur_vaddr = target_vaddr;
//     while (cur_paddr < end_paddr) {
//         error = retype_and_map_frame(cnode_specs, cur_paddr, cur_vaddr, CPTR_VSPACE_ETHERNET_DRIVER, seL4_X86_4K, seL4_ReadWrite);
//         if (error != seL4_NoError) {
//             sddf_dprintf("Error: failed to retype or map a frame.\n");
//             return;
//         }
//         cur_paddr += (1 << seL4_PageBits);
//         cur_vaddr += (1 << seL4_PageBits);
//     }
// }

// uint8_t get_pci_bridge_idx_by_bus(uint8_t pci_bus)
// {
//     for (int i = 0; i < pci_resources->num_devices; i++) {
//         uint8_t num_res = pci_resources->devices[i].num_dev_resources;
//         sddf_dprintf("num_res: %u\n", num_res);
//         for (int j = 0; j < num_res; j++) {
//             device_resource_t *dev_res = (device_resource_t *)&pci_resources->devices[i].dev_resources[j];
//             /* sddf_dprintf("resource type: %u, min_addr: 0x%lx, max_addr: 0x%lx\n", dev_res->type, dev_res->min_addr, dev_res->max_addr); */

//             if (dev_res->type == ACPI_RES_TYPE_BUS) {
//                 if (pci_bus >= dev_res->min_addr && pci_bus < dev_res->max_addr) {
//                     sddf_dprintf("Found the bridge %u[0x%02lx-0x%02lx] containing bus 0x%02x\n", i, dev_res->min_addr, dev_res->max_addr, pci_bus);
//                     return i;
//                 }

//             }
//         }
//     }

//     // TODO: if it's not found
//     return 0;
// }

// /* void configure_msi(struct pci_header_type0 *pci_header, uint8_t vector) */
// /* { */
// /*     struct msix_capability *msix_cap = (struct msix_capability *)find_pci_cap_by_id(pci_header, PCI_CAP_ID_MSIX); */

// /*     if (msix_cap) { */
// /*         // Bits 2-0 refer to BAR ID */
// /*         uint8_t bar_id = msix_cap->table_offset_bir & 0x5; */
// /*         pci_bar_t msix_bar; */
// /*         msix_bar.bar_id = bar_id; */
// /*         /\* msix_bar.base_addr = device_resources.regions[avail_region_idx].io_addr; *\/ */
// /*         msix_bar.ioport = false; */

// /*         map_pci_bar(pci_header, bar_id, 0x4000000); */

// /*         // Enable MSI-X */
// /*         struct msix_msg_ctrl *msg_ctrl = &msix_cap->msg_ctrl; */
// /*         msg_ctrl->msix_enable = 1; */
// /*         sddf_dprintf("Table Size: 0x%x\n", msg_ctrl->table_size + 1); */
// /*         sddf_dprintf("Function Mask: 0x%x\n", msg_ctrl->func_mask); */
// /*         sddf_dprintf("MSI-X Enable: 0x%x\n", msg_ctrl->msix_enable); */

// /*         struct msix_table *msix_table = (struct msix_table *)device_resources.regions[avail_region_idx].region.vaddr; */
// /*         msix_table->msg_addr_low = 0xFEEu << 20; */
// /*         msix_table->msg_data = 0x4030 + vector; */
// /*         msix_table->vec_ctrl = 0x0; */
// /*         sddf_dprintf("Vector 0 Message Addr Low: 0x%x\n", msix_table->msg_addr_low); */
// /*         sddf_dprintf("Vector 0 Message Addr Hi: 0x%x\n", msix_table->msg_addr_hi); */
// /*         sddf_dprintf("Vector 0 Message Data: 0x%x\n", msix_table->msg_data); */
// /*         sddf_dprintf("Vector 0 Vector Control: 0x%x\n", msix_table->vec_ctrl); */

// /*         uint32_t *msix_pba = (uint32_t *)( + 0x800); */
// /*         sddf_dprintf("PBA: 0x%x\n", msix_pba[0]); */

// /*     } */
// /* } */

// acpi_dev_t *find_acpi_dev_by_header_offset(uintptr_t header_offset)
// {
//     uint32_t dev_slot = header_offset >> 15;
//     uint32_t func_slot = (header_offset >> 12) & 0x7;
//     acpi_dev_t *ret_bridge = NULL;

//     sddf_dprintf("Target PCI bridge addr: 0x%lx, dev: 0x%x, func: 0x%x\n", header_offset, dev_slot, func_slot);
//     uint32_t num_devices = pci_resources->num_devices;
//     for (int i = 0; i < num_devices; i++) {
//         acpi_dev_t *pci_bridge = &pci_resources->devices[i];
//         if (ret_bridge != NULL && dev_slot == (pci_bridge->adr >> 16) && func_slot == (pci_bridge->adr & 0xFFFF)) {
//             // Update returned device if the ADR matches both dev_slot and func_slot
//             ret_bridge = pci_bridge;
//         }
//         if (ret_bridge == NULL && dev_slot == (pci_bridge->adr >> 16)) {
//             ret_bridge = pci_bridge;
//         }
//     }

//     sddf_dprintf("pci_bridge addr: 0x%lx\n", ret_bridge->adr);
//     return ret_bridge;
// }

// void bind_irq(acpi_dev_t *pci_bridge, struct pci_header_type0 *pci_header, uint8_t pci_bus, uint8_t pci_dev, uint8_t pci_func, uint8_t irq_num)
// {
//     uint8_t base_irq_cap = 138;

//     uint8_t num_prt_entries = pci_bridge->num_prt_entries;
//     sddf_dprintf("num_prt_entries: %u\n", num_prt_entries);
//     sddf_dprintf("address: 0x%lx\n", (uintptr_t)pci_bridge);
//     uint8_t gsi_number = 0;
//     for (int j = 0; j < num_prt_entries; j++) {
//         pci_prt_t *pci_prt = (pci_prt_t *)&pci_bridge->prt_entries[j];
//         sddf_dprintf("addr: 0x%X, pin: %u, gsi: %u\n", pci_prt->address, pci_prt->pin, pci_prt->gsi);
//         uint32_t dev_num = (pci_prt->address >> 16) & 0x1F;
//         uint32_t func_num = pci_prt->address & 0xFFFF;
//         if (func_num != 0xFFFF) {
//             sddf_dprintf("func numebr: 0x%X, pci_prt->address: 0x%X, &: 0x%X\n", func_num, pci_prt->address, pci_prt->address & 0xFFFF);
//             sddf_dprintf("Error: PRT rule (address: 0x%X, pin: %u, gsi: %u) does not apply to the current implementation\n", pci_prt->address, pci_prt->pin, pci_prt->gsi);
//             return;
//         }

//         if (dev_num == pci_dev) {
//             gsi_number = pci_prt->gsi;
//             sddf_dprintf("Found the GSI numebr %u for the device\n", gsi_number);
//             break;
//         }
//     }

//     if (gsi_number == 0) {
//         sddf_dprintf("Error: failed to find the PRT rule for PCI device at %02x:%02x.%x\n", pci_bus, pci_dev, pci_func);
//         return;
//     }

//     sddf_dprintf("Try creating an IRQ handler capability: ");
//     seL4_Error error = seL4_IRQControl_GetIOAPIC(CPTR_CNODE_PCI_RESOURCES + 1, CPTR_CSPACE_ETHERNET_DRIVER, base_irq_cap + irq_num, 58, 0, gsi_number, 1, 1, 1);
//     if (error != seL4_NoError) {
//         sddf_dprintf("Error: failed to create an IO/APIC IRQ handler - %d\n", error);
//     } else {
//         sddf_dprintf("Success!\n");
//     }

//     sddf_dprintf("Try minting a notification capability: ");
//     error = seL4_CNode_Mint(CPTR_CNODE_PCI_RESOURCES, 511, 58, CPTR_CSPACE_ETHERNET_DRIVER, 1, 58, seL4_ReadWrite, 1 << irq_num);
//     if (error != seL4_NoError) {
//         sddf_dprintf("Error: failed to mint a notification - %d\n", error);
//     } else {
//         sddf_dprintf("Success!\n");
//     }

//     seL4_CPtr handler_cap = CPTR_CSPACE_ETHERNET_DRIVER + base_irq_cap + irq_num;
//     seL4_CPtr ntf_cap = CPTR_CNODE_PCI_RESOURCES + 511;

//     seL4_Word ret = seL4_DebugCapIdentify(handler_cap);
//     sddf_dprintf("ret: %lu\n", ret);
//     sddf_dprintf("Try bind the handler to notification: ");
//     error = seL4_IRQHandler_SetNotification(handler_cap, ntf_cap);
//     if (error != seL4_NoError) {
//         sddf_dprintf("Error: failed to bind to notification - %d\n", error);
//     } else {
//         sddf_dprintf("Success!\n");
//     }
// }

// pci_bridge_node_t *find_parent_pci_bridge(pci_bridge_node_t *bridge_node, uint8_t bus)
// {
//     pci_bridge_node_t *direct_parent_bridge = bridge_node;
//     pci_bridge_node_t *child = bridge_node->child;
//     sddf_dprintf("Looking for bus %u\n", bus);
//     while (child) {
//         sddf_dprintf("secondary: %u, subordinate: %u\n", child->bridge_header->secondary_bus_num, child->bridge_header->subordinate_bus_num);
//         if (child->bridge_header->secondary_bus_num <= bus && bus <= child->bridge_header->subordinate_bus_num) {
//             pci_bridge_node_t *closer_parent_bridge = find_parent_pci_bridge(child, bus);
//             direct_parent_bridge = closer_parent_bridge;
//             break;
//         }
//         child = child->next;
//     }

//     return direct_parent_bridge;
// }

// void config_pci_device(pci_device_config_t *device_config, uintptr_t bus_base, uint8_t bus_start, uint8_t bus_end)
// {
//     struct pci_header_type0 *pci_header = (struct pci_header_type0 *)(bus_base + (device_config->bus << 20) + (device_config->dev << 15) + (device_config->func << 12));
//     pci_bridge_node_t *parent_bridge = find_parent_pci_bridge(host_bridge, device_config->bus);

//     sddf_dprintf("parent_bridge: 0x%lx, header: 0x%lx\n", (uintptr_t)parent_bridge->acpi_dev, (uintptr_t)parent_bridge->bridge_header);
//     for (int i = 0; i < device_config->num_bars; i++) {
//         map_pci_bar(parent_bridge, pci_header, device_config->bars[i].id, device_config->bars[i].vaddr, device_config->bars[i].size);
//     }
//     sddf_dprintf("Finished BAR mapping\n");

//     for (int i = 0; i < device_config->num_irqs; i++) {
//         // FIXME: support only legacy I/O APIC for now
//         bind_irq(parent_bridge->acpi_dev, pci_header, device_config->bus, device_config->dev, device_config->func, device_config->irqs[i].ch);
//     }

//     pci_header->command = pci_header->command | BIT(2) | BIT(1);
// }

// pci_bar_request_t merge_bar_requests(pci_bar_request_t bar_request_a, pci_bar_request_t bar_request_b)
// {
//     pci_bar_request_t bar_request_merged;

//     bar_request_merged.io_16bit = bar_request_a.io_16bit + bar_request_b.io_16bit;
//     bar_request_merged.io_32bit = bar_request_a.io_32bit + bar_request_b.io_32bit;
//     bar_request_merged.mem_32bit_np = bar_request_a.mem_32bit_np + bar_request_b.mem_32bit_np;
//     bar_request_merged.mem_32bit = bar_request_a.mem_32bit + bar_request_b.mem_32bit;
//     bar_request_merged.mem_64bit = bar_request_a.mem_64bit + bar_request_b.mem_64bit;

//     return bar_request_merged;
// }

// pci_bar_request_t scan_and_calc_bar_size(uintptr_t host_bridge_base, pci_bridge_node_t *parent_bridge, uint8_t bus)
// {
//     pci_bar_request_t bar_request_summary = {0, 0, 0, 0, 0};
//     pci_bridge_node_t *child = parent_bridge->child;
//     for (uint8_t pci_dev = 0; pci_dev < 32; pci_dev++) {
//         for (uint8_t pci_func = 0; pci_func < 8; pci_func++) {
//             volatile struct pci_header_type0 *pci_header = (volatile struct pci_header_type0 *)(host_bridge_base + (bus << 20) + (pci_dev << 15) + (pci_func << 12));

//             if (pci_header->vendor_id == 0xffff && pci_header->device_id == 0xffff) continue;
//             sddf_dprintf("bus: 0x%lx, dev: 0x%lx, func: 0x%lx, vendor_id: 0x%x, device_id: 0x%x, type: %u\n",
//                          (((uintptr_t)pci_header >> 20) & 0xff),
//                          (((uintptr_t)pci_header >> 15) & 0x1f),
//                          (((uintptr_t)pci_header >> 12) & 0x7),
//                          pci_header->vendor_id,
//                          pci_header->device_id,
//                          pci_header->header_type & 0x3F);

//             // Clear bit `Bus Master Enable` to disable I/O Requests before re-configuration
//             pci_header->command = pci_header->command & (~BIT(2)) & (~BIT(1));

//             if (pci_header->header_type & 0x3F) {
//                 struct pci_header_type1 *bridge_header = (struct pci_header_type1 *)pci_header;
//                 sddf_dprintf("  - primary bus num: 0x%x\n", bridge_header->primary_bus_num);
//                 sddf_dprintf("  - secondary bus num: 0x%x\n", bridge_header->secondary_bus_num);
//                 sddf_dprintf("  - subordinate bus num: 0x%x\n", bridge_header->subordinate_bus_num);
//                 if (bridge_header->secondary_bus_num > bridge_header->subordinate_bus_num) {
//                     continue;
//                 }

//                 uint32_t bridge_idx = num_pci_bridge_nodes;
//                 num_pci_bridge_nodes++;
//                 pci_bridge_nodes[bridge_idx].parent = parent_bridge;
//                 pci_bridge_nodes[bridge_idx].bridge_header = bridge_header;

//                 if (child) {
//                     child->next = &pci_bridge_nodes[bridge_idx];
//                     child = child->next;
//                 } else {
//                     child = &pci_bridge_nodes[bridge_idx];
//                     parent_bridge->child = child;
//                 }

//                 for (uint8_t child_bridge_bus = bridge_header->secondary_bus_num; child_bridge_bus <= bridge_header->subordinate_bus_num; child_bridge_bus++) {
//                     pci_bar_request_t bar_request = scan_and_calc_bar_size(host_bridge_base, &pci_bridge_nodes[bridge_idx], child_bridge_bus);
//                     bar_request_summary = merge_bar_requests(bar_request_summary, bar_request);
//                 }
//             } else {
//                 for (uint8_t bar_id = 0; bar_id < 6; bar_id++) {
//                     pci_bar_request_t bar_request = read_bar_size((struct pci_header_type0 *)pci_header, bar_id);
//                     if (bar_request.mem_64bit > 0) {
//                         bar_id++;
//                     }
//                     bar_request_summary = merge_bar_requests(bar_request_summary, bar_request);

//                 }
//             }
//         }
//     }

//     parent_bridge->total_req = bar_request_summary;
//     sddf_dprintf("==Bus: %u\n", bus);
//     sddf_dprintf("  - io_16bit: 0x%x\n", bar_request_summary.io_16bit);
//     sddf_dprintf("  - io_32bit: 0x%x\n", bar_request_summary.io_32bit);
//     sddf_dprintf("  - mem_32bit: 0x%x\n", bar_request_summary.mem_32bit);
//     sddf_dprintf("  - mem_64bit: 0x%lx\n", bar_request_summary.mem_64bit);
//     sddf_dprintf("  - mem_32bit_np: 0x%x\n", bar_request_summary.mem_32bit_np);
//     return bar_request_summary;
// }

// void alloc_resource_for_bridges(pci_bridge_node_t *pci_bridge)
// {

//     if (pci_bridge->parent && pci_bridge->parent->is_host_bridge == true) {
//         pci_resource_windows_t allocated_windows = alloc_resource_from_host_bridge(&pci_bridge->total_req);
//         pci_bridge->windows = allocated_windows;

//         acpi_dev_t *acpi_dev = find_acpi_dev_by_header_offset((uint64_t)pci_bridge->bridge_header & ((1 << 28) - 1));
//         if (acpi_dev == NULL) {
//             sddf_dprintf("[Error] ACPI device for bridge is not found\n");
//             return;
//         }
//         pci_bridge->acpi_dev = acpi_dev;
//         sddf_dprintf("==Allocate resource windows:\n");
//         sddf_dprintf("  - io_base: 0x%x\n", pci_bridge->windows.io_base);
//         sddf_dprintf("  - io_size: 0x%x\n", pci_bridge->windows.io_size);
//         sddf_dprintf("  - mem_np_base: 0x%x\n", pci_bridge->windows.mem_np_base);
//         sddf_dprintf("  - mem_np_size: 0x%x\n", pci_bridge->windows.mem_np_size);
//         sddf_dprintf("  - mem_p_base: 0x%lx\n", pci_bridge->windows.mem_p_base);
//         sddf_dprintf("  - mem_p_size: 0x%lx\n", pci_bridge->windows.mem_p_size);
//         sddf_dprintf("  - mem_p_is_64bit: %u\n", pci_bridge->windows.mem_p_is_64bit);

//         volatile struct pci_header_type1 *bridge_header = (volatile struct pci_header_type1 *)pci_bridge->bridge_header;
//         // TODO: check if bridge supports 16bit
//         /* bridge_header->io_base = (uint8_t)pci_bridge->windows.io_base; */
//         /* bridge_header->io_limit = (uint8_t)pci_bridge->windows.io_limit; */
//         sddf_dprintf("==Bridge header before re-allocation\n");
//         sddf_dprintf("  - BAR 0: 0x%x\n", bridge_header->bar0);
//         sddf_dprintf("  - BAR 1: 0x%x\n", bridge_header->bar1);
//         sddf_dprintf("  - io_base: 0x%x\n", bridge_header->io_base);
//         sddf_dprintf("  - io_limit: 0x%x\n", bridge_header->io_limit);
//         sddf_dprintf("  - mem_base: 0x%x\n", bridge_header->mem_base);
//         sddf_dprintf("  - mem_limit: 0x%x\n", bridge_header->mem_limit);
//         sddf_dprintf("  - pre_mem_base: 0x%x\n", bridge_header->pre_mem_base);
//         sddf_dprintf("  - pre_mem_limit: 0x%x\n", bridge_header->pre_mem_limit);
//         sddf_dprintf("  - pre_mem_base_upper: 0x%x\n", bridge_header->pre_mem_base_upper);
//         sddf_dprintf("  - pre_mem_base_limit: 0x%x\n", bridge_header->pre_mem_limit_upper);

//         if (pci_bridge->windows.mem_np_base) {
//             bridge_header->mem_base = (uint16_t)(pci_bridge->windows.mem_np_base >> 16);
//             bridge_header->mem_limit = (uint16_t)((pci_bridge->windows.mem_np_base + pci_bridge->windows.mem_np_size - 1) >> 16);
//         } else {
//             bridge_header->mem_base = 0xFFFF;
//             bridge_header->mem_limit = 0x0000;
//         }

//         // TODO: check if bridge supports 64bit
//         if (pci_bridge->windows.mem_p_base) {
//             bridge_header->pre_mem_base = (uint16_t)(pci_bridge->windows.mem_p_base >> 16);
//             bridge_header->pre_mem_limit = (uint16_t)((pci_bridge->windows.mem_p_base + pci_bridge->windows.mem_p_size - 1) >> 16);
//         } else if (pci_bridge->windows.mem_p_is_64bit) {
//             bridge_header->pre_mem_base_upper = (uint32_t)(pci_bridge->windows.mem_p_base >> 32);
//             bridge_header->pre_mem_limit_upper = (uint32_t)((pci_bridge->windows.mem_p_base + pci_bridge->windows.mem_p_size - 1) >> 32);
//         } else {
//             bridge_header->pre_mem_base = 0xFFFF;
//             bridge_header->pre_mem_limit = 0x0000;
//             bridge_header->pre_mem_base_upper = 0x00000000;
//             bridge_header->pre_mem_limit_upper = 0x00000000;
//         }
//         sddf_dprintf("==Bridge header after re-allocation\n");
//         sddf_dprintf("  - BAR 0: 0x%x\n", bridge_header->bar0);
//         sddf_dprintf("  - BAR 1: 0x%x\n", bridge_header->bar1);
//         sddf_dprintf("  - io_base: 0x%x\n", bridge_header->io_base);
//         sddf_dprintf("  - io_limit: 0x%x\n", bridge_header->io_limit);
//         sddf_dprintf("  - mem_base: 0x%x\n", bridge_header->mem_base);
//         sddf_dprintf("  - mem_limit: 0x%x\n", bridge_header->mem_limit);
//         sddf_dprintf("  - pre_mem_base: 0x%x\n", bridge_header->pre_mem_base);
//         sddf_dprintf("  - pre_mem_limit: 0x%x\n", bridge_header->pre_mem_limit);
//         sddf_dprintf("  - pre_mem_base_upper: 0x%x\n", bridge_header->pre_mem_base_upper);
//         sddf_dprintf("  - pre_mem_base_limit: 0x%x\n", bridge_header->pre_mem_limit_upper);
//         bridge_header->command = bridge_header->command | BIT(2) | BIT(1);

//     } else if (pci_bridge->is_host_bridge == true) {
//         // Do nothing for host bridge
//     } else {
//         sddf_dprintf("[Error] nested bridges are not supported yet\n");
//     }

//     pci_bridge_node_t *child_bridge = pci_bridge->child;
//     while (child_bridge) {
//         alloc_resource_for_bridges(child_bridge);
//         child_bridge = child_bridge->next;
//     }
// }

// void print_cnode_caps()
// {
//     sddf_dprintf("========Descriptions of received capabilities========\n");
//     sddf_dprintf("cnode_caps start: %u, end: %u\n", cnode_specs->start, cnode_specs->end);
//     sddf_dprintf("size of pci_resources_t: %lu\n", sizeof(pci_resources_t));
//     sddf_dprintf("idx,   base_addr,  end_addr\n")
//     sddf_dprintf("%3u: (IRQControl capability)\n", 1);
//     for (int i = cnode_specs->start; i < cnode_specs->end; i++) {
//         sddf_dprintf("%3u: 0x%09lx, 0x%09lx\n", i, cnode_specs->caps[i].base_addr, cnode_specs->caps[i].end_addr);
//     }
// }

// void get_ut_by_paddr(uintptr_t target_paddr)
// {
//     for (int i = cnode_specs->start; i < cnode_specs->end; i++) {
//         if (target_paddr >= cnode_specs->caps[i].base_addr && target_paddr < cnode_specs->caps[i].end_addr) {
//             sddf_dprintf("Found the untyped %u containing the target physical address: 0x%lx\n", i, target_paddr);
//         }
//     }
// }

// void init(void)
// {
//     if (!acpi_ready) {
//         sddf_dprintf("ACPI driver has not set things up. Waiting for signaling\n");
//         return;
//     }

//     // QEMU
//     /* devices_config.devs[0].bus = 0; */
//     /* devices_config.devs[0].dev = 2; */
//     /* devices_config.devs[0].func = 0; */
//     /* devices_config.devs[0].bars[0].id = 4; */
//     /* devices_config.devs[0].bars[0].vaddr = 0x60000000; */
//     /* devices_config.devs[0].bars[0].size = 0x4000; */
//     /* devices_config.devs[0].irqs[0].type = IRQ_IOAPIC; */
//     /* devices_config.devs[0].irqs[0].ch = 16; */
//     /* devices_config.devs[0].num_bars++; */
//     /* devices_config.devs[0].num_irqs++; */
//     /* devices_config.num_dev++; */

//     // Hardware ethernet
//     /* devices_config.devs[0].bus = 1; */
//     /* devices_config.devs[0].dev = 0; */
//     /* devices_config.devs[0].func = 0; */
//     /* devices_config.devs[0].bars[0].id = 0; */
//     /* devices_config.devs[0].bars[0].vaddr = 0x2000000; */
//     /* devices_config.devs[0].bars[0].size = 0x100000; */
//     /* devices_config.devs[0].irqs[0].type = IRQ_IOAPIC; */
//     /* devices_config.devs[0].irqs[0].ch = 16; */
//     /* devices_config.devs[0].num_bars++; */
//     /* devices_config.devs[0].num_irqs++; */
//     /* devices_config.num_dev++; */

//     // Hardware NVMe
//     devices_config.devs[0].bus = 2;
//     devices_config.devs[0].dev = 0;
//     devices_config.devs[0].func = 0;
//     devices_config.devs[0].bars[0].id = 0;
//     devices_config.devs[0].bars[0].vaddr = 0x20000000;
//     devices_config.devs[0].bars[0].size = 0x4000;
//     devices_config.devs[0].irqs[0].type = IRQ_IOAPIC;
//     devices_config.devs[0].irqs[0].ch = 17;
//     devices_config.devs[0].num_bars++;
//     devices_config.devs[0].num_irqs++;
//     devices_config.num_dev++;

//     cnode_specs = (cnode_specs_t *)&pci_resources->cnode_specs;
//     sddf_dprintf("cptr_pci_resources: 0x%lx\n", (uintptr_t)CPTR_CNODE_PCI_RESOURCES);
//     sddf_dprintf("cptr_ethernet_driver: 0x%lx\n", (uintptr_t)CPTR_CSPACE_ETHERNET_DRIVER);
//     cnode_specs->cptr = CPTR_CNODE_PCI_RESOURCES;

//     sddf_dprintf("=========PCI driver is running==========\n");

//     print_cnode_caps();

//     for (int i = 0; i < pci_resources->num_pci_groups; i++) {
//         sddf_dprintf("PCI segment group: %u, base addr: 0x%lx, bus_range: [%u-%u]\n",
//                      pci_resources->pci_seg_groups[i].group_id,
//                      pci_resources->pci_seg_groups[i].base_addr,
//                      pci_resources->pci_seg_groups[i].bus_start,
//                      pci_resources->pci_seg_groups[i].bus_end);
//         pci_seg_group_t *pci_seg_group = &pci_resources->pci_seg_groups[i];
//         uint32_t host_bridge_idx = num_pci_bridge_nodes;
//         pci_bridge_nodes[host_bridge_idx].is_host_bridge = true;
//         host_bridge = &pci_bridge_nodes[host_bridge_idx];
//         num_pci_bridge_nodes++;
//         scan_and_calc_bar_size(pci_seg_group->base_addr, host_bridge, pci_seg_group->bus_start);
//         acpi_dev_t *host_bridge_dev = find_acpi_dev_by_header_offset(0);

//         sddf_dprintf("host_bridge: 0x%lx\n", (uintptr_t)host_bridge_dev);
//         host_bridge->acpi_dev = host_bridge_dev;
//         alloc_resource_for_bridges(host_bridge);

//         for (int j = 0; j < devices_config.num_dev; j++) {
//             config_pci_device(&devices_config.devs[j], pci_seg_group->base_addr, pci_seg_group->bus_start, pci_seg_group->bus_end);
//         }
//     }

//     sddf_deferred_notify(1);
// }

// void notified(microkit_channel ch)
// {
//     sddf_dprintf("\n[PCI driver] notified by ch %d\n", ch);
//     if (ch == 0 && !acpi_ready) {
//         acpi_ready = true;
//         init();
//     }

// }

#include "internal.h"
#include "pci.h"

#define CPTR_POST_ACPI_CNODE  (microkit_cspace_root_slot_to_cptr(1))
#define CPTR_SELF_VSPACE    (microkit_cspace_root_slot_to_cptr(2))

/* In the PCI B:D.F address, device is 5 bits, function is 3 bits. Then each device have a 4K
 * configuration space. */
#define PCI_DEV_BITS 5
#define PCI_FUNC_BITS 3
#define PCIE_SIZE_BYTES_PER_BUS (BIT(PCI_DEV_BITS) * BIT(PCI_FUNC_BITS) * 0x1000)

#define NO_VENDOR 0xffff

#define ACPI_DRIVER_CH 0
acpi_handover_t *post_acpi_handover;

typedef struct {
    void *vaddr;
    mcfg_entry_t desc;
} ecam_t;

typedef struct {
    bool initialised;
    acpi_handover_t *handover;

    uint64_t vaddr_watermark;

    void *ecams_vaddr[ACPI_MAX_NUM_MCFG_ENTRIES];
} pci_drv_state_t;

static pci_drv_state_t drv_state;

static bool map_ecams(pci_drv_state_t *driver_state)
{
    assert(driver_state->handover->num_mcfg_entries <= ACPI_MAX_NUM_MCFG_ENTRIES);
    for (size_t i = 0; i < driver_state->handover->num_mcfg_entries; i++) {
        mcfg_entry_t *mcfg_entry = &driver_state->handover->mcfg_entries[i];

        /* The paddr in the MCFG is not the real base, it starts from bus 0,
         * not mcfg_entry->start_bus, so we need to correct for this */
        uint64_t actual_paddr = mcfg_entry->paddr + ((uint64_t)mcfg_entry->start_bus << 20);
        uint64_t ecam_size_bytes = ((mcfg_entry->end_bus_inclusive + 1) - mcfg_entry->start_bus)
                                 * PCIE_SIZE_BYTES_PER_BUS;
        ecam_size_bytes = ROUND_UP(ecam_size_bytes, BIT(seL4_LargePageBits));

        void *vaddr = (void *)driver_state->vaddr_watermark;

        DEBUG_DRIVER("mapping ECAM for segment %u, start bus %u, end bus %u, paddr 0x%lx, at vaddr 0x%lx, with size "
                     "bytes 0x%lx\n",
                     mcfg_entry->segment, mcfg_entry->start_bus, mcfg_entry->end_bus_inclusive, mcfg_entry->paddr,
                     (uintptr_t)vaddr, ecam_size_bytes);

        if (!map_memory_region(&driver_state->handover->shadow_cnode, CPTR_SELF_VSPACE, actual_paddr, ecam_size_bytes,
                               true, (uintptr_t)vaddr, seL4_ReadWrite, seL4_X86_CacheDisabled)) {
            DEBUG_DRIVER_ERR("mapping unsuccessful\n");
            return false;
        }

        driver_state->ecams_vaddr[i] = vaddr - (mcfg_entry->start_bus * PCIE_SIZE_BYTES_PER_BUS);
        driver_state->vaddr_watermark += ecam_size_bytes;
    }

    DEBUG_DRIVER("All ECAMs mapped\n");
    return true;
}

static bool bus_to_ecam_idx(pci_drv_state_t *driver_state, uint16_t segment, uint8_t bus, size_t *idx)
{
    for (size_t i = 0; i < driver_state->handover->num_mcfg_entries; i++) {
        mcfg_entry_t *mcfg_entry = &driver_state->handover->mcfg_entries[i];
        if (mcfg_entry->segment == segment && bus >= mcfg_entry->start_bus && bus <= mcfg_entry->end_bus_inclusive) {
            *idx = i;
            return true;
        }
    }
    return false;
}

static pci_conf_space_common_hdr_t *pci_bdf_to_conf_space(void *ecam, uint8_t bus, uint8_t dev, uint8_t func)
{
    uintptr_t ecam_base = (uintptr_t)ecam;
    uintptr_t conf_space = ecam_base + ((bus << 20) | (dev << 15) | (func << 12));
    return (pci_conf_space_common_hdr_t *)conf_space;
}

static bool pci_path_equal(const pci_path_t *a, const pci_path_t *b)
{
    if (a->depth != b->depth) {
        return false;
    }
    for (uint8_t i = 0; i < a->depth; i++) {
        if (a->devfn[i] != b->devfn[i]) {
            return false;
        }
    }
    return true;
}

/* This is part of the bread and butter of the PCIe driver. The device's configuration space
 * only tells software what INTx pin (A, B, C or D) it is using. Using the PCI Routing Tables
 * (PRTs) from the firmware DSDT/SSDTs, we must work out what Global System Interrupt (GSI)
 * the INTx pin of this particular device maps to. Then later the code will map the GSI into
 * an I/O APIC chip and pin.
 *
 * The device may be behind several bridges. A bridge only has four interrupt pins going up,
 * shared by everything below it, and it rotates them by slot so devices don't all pile onto
 * INTA: pin P of the device in slot S comes out of the bridge as pin (P + S) % 4. If a bridge
 * has no PRT, we apply this "swizzle" ourselves, then repeat the lookup with the bridge as
 * the device, one level up.
 *
 * `path` must contain the route from the host bridge to `dev`'s parent bridge. It doesn't need
 * bus numbers, as each hop's dev.fn is relative to the bus the previous hop leads to. `pin` is
 * 0-based (INTA = 0), unlike the 1-based Interrupt Pin register in configuration space.
 *
 * Returns the matching PRT entry (GSI, trigger and polarity) from all the PRTs recorded
 * against the host bridge by the ACPI driver, or NULL if the firmware didn't describe one.
 */
static prt_entry_t *intx_to_prt(host_bridge_t *hb, pci_path_t path, uint8_t dev, uint8_t pin)
{
    for (;;) {
        bool have_table = false;

        for (size_t i = 0; i < hb->num_prt_entries; i++) {
            prt_entry_t *e = &hb->prt_entries[i];
            if (!pci_path_equal(&e->bridge_path, &path)) {
                continue;
            }
            have_table = true;
            if (e->dev == dev && e->pin == pin) {
                return e;
            }
        }

        if (have_table) {
            uint8_t bridge = path.devfn[path.depth - 1];
            DEBUG_DRIVER_ERR("Firmware bug: _PRT of bridge %02x.%x (depth %u) has no entry for slot %u INT%c\n",
                             bridge >> 3, bridge & 0x7, path.depth, dev, 'A' + pin);
            return NULL;
        }
        if (path.depth == 0) {
            DEBUG_DRIVER_ERR("Firmware did not describe INTx routing: no _PRT on any bridge up to the host "
                             "bridge, can't route slot %u INT%c on the root bus. Probably MSI only?\n",
                             dev, 'A' + pin);
            return NULL;
        }

        /* no _PRT here: swizzle and treat the bridge as the device we are looking for itself */
        pin = (pin + dev) % 4;
        path.depth--;
        dev = path.devfn[path.depth] >> 3;
    }
}

static bool handle_pcie_endpoint(pci_drv_state_t *driver_state, host_bridge_t *hb,
                                 volatile pci_conf_space_endpoint_t *endpoint_cs, uint8_t bus, uint8_t dev,
                                 uint8_t func, pci_path_t path)
{
    if (endpoint_cs->interrupt_pin) {
        /* -1 to match ACPI PRT's 0-indexing */
        uint8_t int_pin = endpoint_cs->interrupt_pin - 1;
        prt_entry_t *prt = intx_to_prt(hb, path, dev, int_pin);
        if (!prt) {
            return false;
        }

        DEBUG_DRIVER("\t\tInterrupt Pin: %u, GSI: %u\n", int_pin, prt->gsi);
    }

    for (int i = 0; i < PCI_TYPE_0_NUM_BARS; i++) {
        /* Don't care about I/O Space, for now... */
        uint32_t orig_bar_value = endpoint_cs->bars[i];
        if (orig_bar_value & PCI_BAR_IO_SPACE_MASK) {
            continue;
        }

        /* From https://wiki.osdev.org/PCI:
        * "Before attempting to read the information about the BAR, make sure to disable
        *  both I/O and memory decode in the command byte. You can restore the original
        *  value after completing the BAR info read. This is needed as some devices are
        *  known to decode the write of all ones to the register as an (unintended) access."
        */
        uint16_t orig_cmd = endpoint_cs->hdr.command;
        endpoint_cs->hdr.command = orig_cmd & ~PCI_COMMAND_IO_SPACE_MASK & ~PCI_COMMAND_MEM_SPACE_MASK;

        uint32_t orig_bar_value_high = 0;
        bool is_64_bit = ((orig_bar_value >> 1) & 0x3) == 0x2;
        if (is_64_bit) {
            if (i == PCI_TYPE_0_NUM_BARS - 1) {
                DEBUG_DRIVER_ERR("Firmware bug: last BAR can't be 64-bit!\n");
                goto read_bar_complete;
            }
            orig_bar_value_high = endpoint_cs->bars[i + 1];
        }

        /* Read size */
        uint32_t lo_rb = 0;
        uint32_t hi_rb = 0xffffffff;   /* 32-bit BAR: pretend the high half read back all ones */

        endpoint_cs->bars[i] = 0xffffffff;
        lo_rb = endpoint_cs->bars[i];
        endpoint_cs->bars[i] = orig_bar_value;

        if (is_64_bit) {
            endpoint_cs->bars[i + 1] = 0xffffffff;
            hi_rb = endpoint_cs->bars[i + 1];
            endpoint_cs->bars[i + 1] = orig_bar_value_high;
        }

        if ((lo_rb & PCI_BAR_ADDR_MASK) == 0 && (!is_64_bit || hi_rb == 0))
            goto read_bar_complete;               /* BAR not implemented */

        uint64_t mask = ((uint64_t)hi_rb << 32) | (lo_rb & PCI_BAR_ADDR_MASK);
        uint64_t bar_size_bytes = ~mask + 1;

        uint64_t paddr = (orig_bar_value & PCI_BAR_ADDR_MASK) | (((uint64_t)orig_bar_value_high) << 32);
        bool prefetchable = orig_bar_value & PCI_BAR_PREFETCHABLE_MASK ? true : false;

        DEBUG_DRIVER("\t\tBAR %u: paddr 0x%lx, size: 0x%lx prefetchable: %s\n", i, paddr, bar_size_bytes,
                     prefetchable ? "yes" : "no");

    read_bar_complete:
        endpoint_cs->hdr.command = orig_cmd;
        if (is_64_bit) {
            i++;
        }
    }

    return true;
}

static bool bus_scan_recursive(pci_drv_state_t *driver_state, host_bridge_t *hb, void *ecam, uint8_t bus,
                               pci_path_t path);

static bool handle_pcie_bridge(pci_drv_state_t *driver_state, host_bridge_t *hb, void *ecam,
                               volatile pci_conf_space_bridge_t *bridge_cs, uint8_t bus, uint8_t dev, uint8_t func,
                               pci_path_t path)
{
    uint8_t secondary = bridge_cs->secondary_bus_num;
    uint8_t subordinate = bridge_cs->subordinate_bus_num;
    if (secondary > bus && secondary <= subordinate) {
        pci_path_t new_path = path;
        if (new_path.depth == PCI_MAX_PATH_DEPTH) {
            DEBUG_DRIVER_ERR("topology too deep, consider increasing PCI_MAX_PATH_DEPTH\n");
            return false;
        }

        new_path.devfn[new_path.depth++] = (dev << 3) | func;
        bus_scan_recursive(driver_state, hb, ecam, secondary, new_path);
    } else {
        DEBUG_DRIVER_ERR("bridge %02x:%02x.%x unconfigured\n", bus, dev, func);
        // @billn todo, assign bus number and whatnot
    }

    return true;
}

static bool bus_scan_recursive(pci_drv_state_t *driver_state, host_bridge_t *hb, void *ecam, uint8_t bus,
                               pci_path_t path)
{
    for (uint8_t dev = 0; dev < BIT(PCI_DEV_BITS); dev++) {
        for (uint8_t func = 0; func < BIT(PCI_FUNC_BITS); func++) {
            volatile pci_conf_space_common_hdr_t *common_hdr = pci_bdf_to_conf_space(ecam, bus, dev, func);

            if (common_hdr->vendor_id == NO_VENDOR) {
                if (func == 0) {
                    /* nothing in this slot */
                    break;
                }
                /* gap in a multi-function device */
                continue;
            }

            DEBUG_DRIVER("\t%02x:%02x.%x:\n", bus, dev, func);
            DEBUG_DRIVER("\t\tVendor: 0x%04X, Device: 0x%04X\n", common_hdr->vendor_id, common_hdr->device_id);
            DEBUG_DRIVER("\t\tClass: %s\n",
                         pci_class_and_subclass_to_string(common_hdr->class_code, common_hdr->subclass));

            uint8_t hdr_type = common_hdr->header_type & 0x7f;
            if (hdr_type == 0) {
                volatile pci_conf_space_endpoint_t *endpoint_cs = (pci_conf_space_endpoint_t *)common_hdr;
                if (!handle_pcie_endpoint(driver_state, hb, endpoint_cs, bus, dev, func, path)) {
                    return false;
                }
            } else if (hdr_type == 1) {
                volatile pci_conf_space_bridge_t *bridge_cs = (pci_conf_space_bridge_t *)common_hdr;
                if (!handle_pcie_bridge(driver_state, hb, ecam, bridge_cs, bus, dev, func, path)) {
                    return false;
                }
            }

            if (func == 0 && !(common_hdr->header_type & 0x80))
                /* single-function device */
                break;
        }
    }

    return true;
}

/* For each host bridge described by the firmware DSDT/SSDTs, scan it for the devices we care about.
 * Then, for each said device, work out their:
 * 1. Global System Interrupt (GSI) number
 * 2. Base Address Registers (BARs) paddr and sizes. Assign them if firmware had not assign them. */
static bool host_bridges_scan(pci_drv_state_t *driver_state)
{
    for (size_t hb = 0; hb < driver_state->handover->num_host_bridges; hb++) {
        host_bridge_t *hb_desc = &driver_state->handover->host_bridges[hb];

        size_t ecam_idx;
        uint16_t segment = hb_desc->segment;
        uint8_t bus = hb_desc->root_bus;
        if (!bus_to_ecam_idx(driver_state, segment, bus, &ecam_idx)) {
            DEBUG_DRIVER_ERR("Firmware bug: failed to look up ECAM for host bridge with segment %u, root bus %u\n",
                             hb_desc->segment, hb_desc->root_bus);
            return false;
        }
        assert(ecam_idx <= driver_state->handover->num_mcfg_entries);
        void *ecam_vaddr = driver_state->ecams_vaddr[ecam_idx];

        DEBUG_DRIVER("Host bridge segment %u, root bus %u:\n", segment, bus);

        pci_path_t path = { .depth = 0 };
        if (!bus_scan_recursive(driver_state, hb_desc, ecam_vaddr, bus, path)) {
            return false;
        }
    }

    return true;
}

void init(void)
{
    memset(&drv_state, 0, sizeof(drv_state));
    drv_state.vaddr_watermark = BIT(32);
    drv_state.handover = post_acpi_handover;

    DEBUG_DRIVER("Blocking on ACPI driver handover\n");
    microkit_msginfo msginfo = microkit_msginfo_new(0, 0);
    microkit_ppcall(ACPI_DRIVER_CH, msginfo);
    DEBUG_DRIVER("ACPI driver handover complete\n");

    if (post_acpi_handover->magic != ACPI_HANDOVER_MAGIC) {
        DEBUG_DRIVER_ERR("ACPI handover have bad magic: %x != %x\n", post_acpi_handover->magic, ACPI_HANDOVER_MAGIC);
        return;
    }

#ifdef CONFIG_DEBUG_DRIVER
    dump_acpi_info(post_acpi_handover);
#endif

    if (!map_ecams(&drv_state))
        return;
    if (!host_bridges_scan(&drv_state))
        return;

    drv_state.initialised = true;
}

void notified(microkit_channel ch)
{
    DEBUG_DRIVER_ERR("Unexpected notification on channel %u\n", ch);
}

seL4_MessageInfo_t protected(microkit_channel ch, microkit_msginfo msginfo)
{
    if (!drv_state.initialised) {
        return microkit_msginfo_new(0, 0);
    }
    return microkit_msginfo_new(0, 0);
}