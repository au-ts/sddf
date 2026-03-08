#include <dma.h>
#include <stdint.h>
#include <common/tusb_verify.h>
#include <common/tusb_debug.h>

static char *allocated_before = (char *) DMA_START;

void *dmalloc(unsigned size) {
    uint64_t remainder = (uint64_t) allocated_before % PAGE_SIZE;
    if (remainder) {
        /* align to page */
        allocated_before += (PAGE_SIZE - remainder);
    }

    TU_ASSERT(size + allocated_before <= (char *) (DMA_START + DMA_SIZE));

    void *allocation = allocated_before;
    allocated_before += size;

    return allocation;
}