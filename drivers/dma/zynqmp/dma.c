/*
 * Copyright 2025, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Documents referenced: Zynq UltraScale+ Device TRM, UG1085 (v2.5) March 21, 2025.
 *                       Zynq UltraScale+ Devices Register Reference (UG1087)
 */

#include <os/sddf.h>
#include <sddf/util/cache.h>
#include <sddf/util/printf.h>

#include <dma.h>

// __attribute__((section (".CCI_GPV_S3"))) uint64_t CCI_GPV_S3 = {};
// #define Snoop_Control_Register_S3 0x4000

// LPD DMA
__attribute__((__section__(".zdma_adma_ch0"))) uint64_t zdma_adma_ch0 = {};

__attribute__((__section__(".shared_memory"))) uint64_t shared_memory = {};

#define ZDMA_CH zdma_adma_ch0

// #define PM_MMIO_READ 0xC2000014U
// #define Snoop_Control_Register_S3 0x4000
// __attribute__((section (".CCI_GPV_S3"))) uint64_t CCI_GPV_S3 = {};

static void make_dma_coherent()
{
    // cannot access the register even under non-secure EL2
    {
        // seL4_ARM_SMCContext args = {
        //     .x0 = PM_MMIO_READ,
        //     .x1 = CCI_GPV_S3 + Snoop_Control_Register_S3,
        // };
        // seL4_ARM_SMCContext response = {};
        // microkit_arm_smc_call(&args, &response);
        microkit_dbg_puts("TODO");
        microkit_internal_crash(0);
        // auto ctrl = _load32("Snoop_Control_Register_S3", CCI_GPV_S3 + Snoop_Control_Register_S3);
        // ctrl |= 1;
        // _store32("Snoop_Control_Register_S3", CCI_GPV_S3 + Snoop_Control_Register_S3, ctrl);
    }
    {
        auto data_attr = load(DATA_ATTR);
        data_attr = modify(data_attr, AWCACHE, 0xB);
        data_attr = modify(data_attr, ARCACHE, 0xB);
        store(DATA_ATTR, data_attr);
    }
}

static void wait()
{
    while (1) {
        auto status = load(STATUS) & 0b11U;
        if (status == 0) {
            sddf_dprintf("%s: no error\n", __func__);
            break;
        }
        if (status == 1) {
            sddf_dprintf("%s: paused with no error\n", __func__);
        } else if (status == 2) {
            sddf_dprintf("%s: DMA is busy transferring\n", __func__);
        } else if (status == 3) {
            sddf_dprintf("%s: DMA done with error\n", __func__);
        }
    }
}

void init(void)
{
    // make_dma_coherent();
    // store(IEN, 0xFFF);

    auto ch_ctrl0 = load(CTRL0);
    if (ch_ctrl0 & POINT_TYPE) {
        ch_ctrl0 = modify(ch_ctrl0, POINT_TYPE, 0);
        store(CTRL0, ch_ctrl0);
    }
}

void notified([[maybe_unused]] microkit_channel ch)
{
}

microkit_msginfo protected([[maybe_unused]] microkit_channel ch, [[maybe_unused]] microkit_msginfo msginfo)
{
    auto dest_vaddr = shared_memory + microkit_mr_get(0);
    auto src_vaddr = shared_memory + microkit_mr_get(1);
    auto count = microkit_mr_get(2);

    cache_clean(src_vaddr, src_vaddr + count);

    wait();

    store(SRC_DSCR_LO, src_vaddr & UINT32_MAX);
    store(SRC_DSCR_HI, src_vaddr >> 32U);
    store(DST_DSCR_LO, dest_vaddr & UINT32_MAX);
    store(DST_DSCR_HI, dest_vaddr >> 32U);
    store(SRC_DSCR_SIZE, count & SIZE);
    store(DST_DSCR_SIZE, count & SIZE);
    store(CTRL2, EN);

    wait();

    cache_clean_and_invalidate(dest_vaddr, dest_vaddr + count);

    return microkit_msginfo_new(0, 0);
}
