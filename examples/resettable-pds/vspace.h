#pragma once

#include <microkit.h>
#include <stddef.h>

#define NUM_DEBUGEES 2

uint32_t libvspace_read_word(uint16_t client, uintptr_t addr, seL4_Word *val);
uint32_t libvspace_write_word(uint16_t client, uintptr_t addr, seL4_Word val);
void libvspace_set_small_mapping_region(uint64_t vaddr);
void libvspace_set_large_mapping_region(uint64_t vaddr);

uint32_t libvspace_write_bytes(uint16_t client, uintptr_t start_addr, char *bytes, size_t nbytes);
