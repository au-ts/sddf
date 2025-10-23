#include <stdint.h>
#include <sddf/util/printf.h>

#define SBI_BASE_EID 0x10
#define SBI_PMU_EID 0x504D55

#define SBI_PMU_FID_NUM_COUNTERS 0x0
#define SBI_PMU_FID_COUNTER_GET_INFO 0x1

void riscv_dump_pmu_info() {
    seL4_RISCV_SBIContext sbi_args;
    seL4_RISCV_SBIRet sbi_ret;

    sbi_args.a6 = 0;
    sbi_args.a7 = 0x10;
    seL4_RISCV_SBI_Call(RISCV_SBI_CAP, &sbi_args, &sbi_ret);

    seL4_Word sbi_version = sbi_ret.value;
    sddf_printf("SBI version: %lu.%lu\n", (sbi_version >> 24) & ((1 << 7) - 1), sbi_version & ((1 << 24) - 1));

    sbi_args.a6 = SBI_PMU_FID_NUM_COUNTERS;
    sbi_args.a7 = SBI_PMU_EID;
    seL4_RISCV_SBI_Call(RISCV_SBI_CAP, &sbi_args, &sbi_ret);

    seL4_Word num_counters = sbi_ret.value;
    sddf_printf("SBI num counters: %lu\n", num_counters);

    for (int i = 0; i < num_counters; i++) {
        sddf_printf("SBI counter %d getting info\n", i);
        sbi_args.a0 = i;
        sbi_args.a6 = SBI_PMU_FID_COUNTER_GET_INFO;
        sbi_args.a7 = SBI_PMU_EID;
        seL4_RISCV_SBI_Call(RISCV_SBI_CAP, &sbi_args, &sbi_ret);

        sddf_printf("SBI counter(%d): 0x%x\n", i, sbi_ret.value);
    }
}
