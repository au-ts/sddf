#include <stdint.h>
#include <sddf/util/printf.h>

#define SBI_VERSION_MINOR(version) (version & ((1 << 24) - 1))
#define SBI_VERSION_MAJOR(version) ((version >> 24) & ((1 << 7) - 1))

#define SBI_BASE_EID 0x10
#define SBI_PMU_EID 0x504D55

#define SBI_BASE_SPEC_VERSION_FID 0x0
#define SBI_BASE_PROBE_FID 0x3

#define SBI_PMU_FID_NUM_COUNTERS 0x0
#define SBI_PMU_FID_COUNTER_GET_INFO 0x1
#define SBI_PMU_FID_COUNTER_CONFIG_MATCHING 0x2
#define SBI_PMU_FID_COUNTER_START 0x3
#define SBI_PMU_FID_COUNTER_STOP 0x4
#define SBI_PMU_FID_COUNTER_READ 0x5

#define SBI_PMU_START_SET_INIT_VALUE (1)

/* SBI PMU event types */
#define SBI_PMU_HW_TYPE_EVENTS 0

/* SBI PMU hardware events */
#define SBI_PMU_HW_NO_EVENT 0
#define SBI_PMU_HW_CPU_CYCLES 1
#define SBI_PMU_HW_INSTRUCTIONS 2
#define SBI_PMU_HW_CACHE_REFERENCES 3
#define SBI_PMU_HW_CACHE_MISSES 4
#define SBI_PMU_HW_BRANCH_INSTRUCTIONS 5
#define SBI_PMU_HW_BRANCH_MISSES 6
#define SBI_PMU_HW_BUS_CYCLES 7
#define SBI_PMU_HW_STALLED_CYCLES_FRONTEND 8
#define SBI_PMU_HW_STALLED_CYCLES_BACKEND 9
#define SBI_PMU_HW_REF_CPU_CYCLES 10

seL4_RISCV_SBIRet sbi_call(seL4_Word eid, seL4_Word fid, seL4_Word a0, seL4_Word a1, seL4_Word a2, seL4_Word a3, seL4_Word a4, seL4_Word a5) {
    seL4_RISCV_SBIContext sbi_args = {0};
    seL4_RISCV_SBIRet sbi_ret = {0};

    sbi_args.a0 = a0;
    sbi_args.a1 = a1;
    sbi_args.a2 = a2;
    sbi_args.a3 = a3;
    sbi_args.a4 = a4;
    sbi_args.a5 = a5;

    sbi_args.a6 = fid;
    sbi_args.a7 = eid;

    seL4_Error err = seL4_RISCV_SBI_Call(RISCV_SBI_CAP, &sbi_args, &sbi_ret);
    assert(err == seL4_NoError);

    return sbi_ret;
}

seL4_Word event_idx(uint8_t type, uint16_t code) {
    return ((uint32_t)type << 16) | (code);
}

uint64_t riscv_read_counter(unsigned int counter) {
    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_PMU_EID, SBI_PMU_FID_COUNTER_READ, counter, 0, 0, 0, 0, 0);
    if (sbi_ret.error) {
        sddf_printf("ERROR: could not read counter %u: %ld\n", counter, sbi_ret.error);
    }
    assert(!sbi_ret.error);

    return sbi_ret.value;
}

void riscv_start_counter(unsigned int counter, unsigned long start_flags, uint64_t initial_value) {
    unsigned long counter_idx_base = 0;
    unsigned long counter_idx_mask = 1 << counter;

    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_PMU_EID, SBI_PMU_FID_COUNTER_START, counter_idx_base, counter_idx_mask, start_flags, initial_value, 0, 0);

    if (sbi_ret.error) {
        sddf_printf("ERROR: could not start counter %d: %ld\n", counter, sbi_ret.error);
    }
    assert(!sbi_ret.error);
}

void riscv_stop_counter(unsigned int counter, unsigned long stop_flags) {
    unsigned long counter_idx_base = 0;
    unsigned long counter_idx_mask = 1 << counter;

    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_PMU_EID, SBI_PMU_FID_COUNTER_STOP, counter_idx_base, counter_idx_mask, stop_flags, 0, 0, 0);

    assert(!sbi_ret.error);
}

void riscv_configure_counter(unsigned int counter, unsigned long config_flags, unsigned long event_idx, uint64_t event_data) {
    unsigned long counter_idx_base = 0;
    unsigned long counter_idx_mask = 1 << counter;

    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_PMU_EID, SBI_PMU_FID_COUNTER_CONFIG_MATCHING, counter_idx_base, counter_idx_mask, config_flags, event_idx, event_data, 0);
    assert(!sbi_ret.error);

    assert(sbi_ret.value == counter);
}

seL4_Word riscv_num_counters() {
    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_PMU_EID, SBI_PMU_FID_NUM_COUNTERS, 0, 0, 0, 0, 0, 0);
    assert(!sbi_ret.error);

    return sbi_ret.value;
}

seL4_Word riscv_counter_info(unsigned long counter) {
    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_PMU_EID, SBI_PMU_FID_COUNTER_GET_INFO, counter, 0, 0, 0, 0, 0);
    assert(!sbi_ret.error);

    return sbi_ret.value;
}

bool riscv_sbi_eid_exists(seL4_Word eid) {
    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_BASE_EID, SBI_BASE_PROBE_FID, eid, 0, 0, 0, 0, 0);
    assert(!sbi_ret.error);

    return (sbi_ret.value == 1);
}

seL4_Word riscv_sbi_version() {
    seL4_RISCV_SBIRet sbi_ret = sbi_call(SBI_BASE_EID, SBI_BASE_SPEC_VERSION_FID, 0, 0, 0, 0, 0, 0);
    assert(!sbi_ret.error);

    return sbi_ret.value;
}

void riscv_dump_pmu_info() {
    seL4_Word sbi_version = riscv_sbi_version();
    sddf_printf("SBI version: %lu.%lu\n", SBI_VERSION_MAJOR(sbi_version), SBI_VERSION_MINOR(sbi_version));

    assert(!riscv_sbi_eid_exists(0x1231321));
    assert(riscv_sbi_eid_exists(SBI_BASE_EID));

    if (!riscv_sbi_eid_exists(SBI_PMU_EID)) {
        sddf_printf("ERROR: SBI PMU extension ID is not available\n");
        return;
    }

    seL4_Word num_counters = riscv_num_counters();
    sddf_printf("SBI num counters: %lu\n", num_counters);
    for (int i = 0; i < num_counters; i++) {
        sddf_printf("SBI counter(%d): 0x%lx\n", i, riscv_counter_info(i));
    }

    // seL4_Word cycle_count;
    // for (int i = 0; i < 100; i++) {
    //     asm volatile("rdcycle %0" :"=r"(cycle_count));
    //     sddf_printf("cycle count: %lu\n", cycle_count);
    // }

    // sddf_printf("Configuring counter 0\n");

    // riscv_configure_counter(0, 0, event_idx(SBI_PMU_HW_TYPE_EVENTS, SBI_PMU_HW_CPU_CYCLES), 0);
    // riscv_stop_counter(0, 0);
    // riscv_start_counter(0, SBI_PMU_START_SET_INIT_VALUE, 0);
    // for (int i = 0; i < 100; i++) {
    //     sddf_printf("counter value: %lu\n", riscv_read_counter(0));
    // }
    // riscv_stop_counter(0, 0);
}
