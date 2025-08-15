#pragma once

#include <stdint.h>

#include <sddf/util/printf.h>

#define ISR            0x100U
#define DST_DSCR_DONE (1U << 2U)
#define DMA_DONE    (1U << 10U)
#define IEN            0x108U
#define CTRL0          0x110U
#define STATUS         0x11CU
#define POINT_TYPE  (1U << 6U)
#define DATA_ATTR      0x120U
#define AWCACHE     (0xFU << 8U)
#define ARCACHE     (0xFU << 22U)
#define SRC_DSCR_LO    0x128U
#define SRC_DSCR_HI    0x12CU
#define SRC_DSCR_SIZE  0x130U
#define SIZE         0x3FFFFFFFU
#define SRC_DSCR_CTRL  0x134U
#define COHRNT      (1U << 0U)
#define INTR        (1U << 2U)
#define DST_DSCR_LO    0x138U
#define DST_DSCR_HI    0x13CU
#define DST_DSCR_SIZE  0x140U
#define DST_DSCR_CTRL  0x144U
#define CTRL2          0x200U
#define EN (1U << 0U)

static uint32_t load32([[maybe_unused]] const char *name, uint64_t addr)
{
    sddf_dprintf("[load] %s = ", name);
    auto ret = *((volatile const uint32_t *)addr);
    sddf_dprintf("0x%x\n", ret);
    return ret;
}
#define load(x) load32(#x, ZDMA_CH + (x))

static void store32([[maybe_unused]] const char *name, uint64_t addr, uint32_t value)
{
    sddf_dprintf("[store] %s = 0x%x\n", name, value);
    *((volatile uint32_t *)addr) = value;
}
#define store(x, v) store32(#x, ZDMA_CH + (x), v)

static uint32_t modify(uint32_t src, uint32_t mask, uint32_t value)
{
    return (src & (~mask)) | ((value << (uint32_t)__builtin_ctz(mask)) & mask);
}
