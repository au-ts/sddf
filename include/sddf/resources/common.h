#pragma once

#include <stdint.h>

typedef struct region_resource {
    void *vaddr;
    uintptr_t paddr;
    uint64_t size;
} region_resource_t;
