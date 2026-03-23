#include <stdbool.h>
#include <string.h>
#include <sddf/util/printf.h>
#include "ramfb.h"

// Addresses for the fw_cfg registers (source - https://github.com/qemu/qemu/blob/db596ae19040574e41d086e78469014191d7d7fc/hw/arm/virt.c#L137).
#define fw_cfg_address ((volatile uint8_t*)0x09020000)
#define selector_register ((volatile uint16_t*)(fw_cfg_address + 8))
#define data_register ((volatile uint64_t*)(fw_cfg_address + 0))
#define dma_address ((volatile uint64_t*)(fw_cfg_address + 16))

// Structs needed for fw_cfg DMA access.

struct QemuCfgDmaAccess {
    uint32_t control;
    uint32_t length;
    uint64_t address;
} __attribute__((packed));

struct FWCfgFile {
    uint32_t size;
    uint16_t select;
    uint16_t reserved;
    char name[56];
} __attribute__((packed));

struct FWCfgFiles {
    uint32_t count;
    struct FWCfgFile files[];
} __attribute__((packed));

// Functions to interface with fw_cfg.

void fw_cfg_write_selector(uint16_t selector) {
    *selector_register = BE16(selector);
}

uint64_t fw_cfg_read_data() {
    return *data_register;
}

void fw_cfg_dma_transfer(volatile void* address, uint32_t length, uint32_t control) {
    volatile struct QemuCfgDmaAccess *dma = (volatile struct QemuCfgDmaAccess *)DMA_CONTROL_VADDR;
    dma->control = BE32(control);
    dma->address = BE64((uint64_t)address);
    dma->length = BE32(length);

    sddf_dprintf("DMA at 0x%p of length: 0x%x\n", address, length);

    *dma_address = BE64(DMA_CONTROL_PADDR);
    sddf_dprintf("DMA TRANFSER: going\n");
    while (BE32(dma->control) & ~0x01);
    sddf_dprintf("DMA TRANFSER: done\n");
}

void fw_cfg_dma_read(volatile void* buf, int e, int length) {
    uint32_t control = (e << 16) | 0x08 | 0x02;
    fw_cfg_dma_transfer(DMA_ADDRESS_PADDR, length, control);
    memcpy((void *)buf, (void *)DMA_ADDRESS_VADDR, length);
}

void fw_cfg_dma_write(void* buf, int e, int length) {
    uint32_t control = (e << 16) | 0x08 | 0x10;
    memcpy((void *)DMA_ADDRESS_VADDR, buf, length);
    fw_cfg_dma_transfer(DMA_ADDRESS_PADDR, length, control);
}

// Finds the requested file name from fw_cfg.
bool fw_cfg_find_file(struct FWCfgFile* out, const char* name) {
    uint64_t name_size = strlen(name);
    volatile uint32_t files_count = 0;
    fw_cfg_dma_read(&files_count, 0x19, sizeof(files_count));
    files_count = BE32(files_count);
    sddf_dprintf("RAMFB: files_count: %d\n", files_count);

    // Since we don't have a memory allocator or buffer, we have to use the stack to store the directory.
    uint64_t directory_size = sizeof(struct FWCfgFiles) + (sizeof(struct FWCfgFile) * files_count);
    struct FWCfgFiles* directory = __builtin_alloca(directory_size);
    fw_cfg_dma_read(directory, 0x19, directory_size);

    for (int i = 0; i < files_count; i++) {
        struct FWCfgFile* file = &directory->files[i];
        sddf_dprintf("RAMFB: file %s\n", file->name);
        if (!memcmp(name, file->name, name_size)) {
            sddf_dprintf("RAMFB: found %s\n", file->name);
            file->size = BE32(file->size);
            file->select = BE16(file->select);
            *out = *file;

            return true;
        }
    }
    return false;
}


// Global functions.

void qemu_ramfb_configure(struct QemuRamFBCfg* cfg) {
    // Find ramfb handle.
    struct FWCfgFile ramfb_file;
    bool found = fw_cfg_find_file(&ramfb_file, "etc/ramfb");
    assert(found);

    // Configure ramfb.
    fw_cfg_dma_write(cfg, ramfb_file.select, sizeof(struct QemuRamFBCfg));
}

void qemu_ramfb_make_cfg(struct QemuRamFBCfg* cfg, void* fb_address, uint32_t fb_width, uint32_t fb_height) {
    cfg->address = BE64((uint64_t)fb_address);
    cfg->fourcc = BE32(FORMAT_XRGB8888);
    cfg->width = BE32(fb_width);
    cfg->height = BE32(fb_height);
    cfg->flags = BE32(0);
    cfg->stride = BE32(fb_width * sizeof(uint32_t));
}
