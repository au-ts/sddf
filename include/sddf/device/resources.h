#include <stdint.h>

#define DEVICE_MAX_REGIONS 64
#define DEVICE_MAX_IRQS 64

typedef struct device_region_resource {
    void *vaddr;
    uint64_t paddr;
    uint64_t size;
} device_region_resource_t;

typedef struct device_irq_resource {
    uint8_t id;
} device_irq_resource_t;

typedef struct device_resources {
    uint8_t num_regions;
    uint8_t num_irqs;
    device_region_resource_t regions[DEVICE_MAX_REGIONS];
    device_irq_resource_t irqs[DEVICE_MAX_IRQS];
} device_resources_t;
