/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <stdbool.h>
#include <microkit.h>
#include <sel4/benchmark_track_types.h>
#include <sel4/benchmark_utilisation_types.h>
#include <sddf/benchmark/sel4bench.h>
#include <sddf/benchmark/config.h>
#include <sddf/serial/queue.h>
#include <sddf/serial/config.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

#define LOG_BUFFER_CAP 7

__attribute__((__section__(".benchmark_config"))) benchmark_config_t benchmark_config;

__attribute__((__section__(".serial_client_config"))) serial_client_config_t serial_config;

// This could be moved to a vm config.h file
#define BENCH_VM_MAGIC_LEN 5
static const char BENCH_VM_MAGIC[BENCH_VM_MAGIC_LEN] = { 'B', 'V', 'M', 'C', 0x1 };

typedef struct {
    uint64_t results_vaddr;
    char magic[BENCH_VM_MAGIC_LEN];
    uint8_t ch_start;
    uint8_t ch_stop;
    uint8_t ch_done;
    uint8_t vcpu_id;
    char vm_name[SDDF_NAME_LENGTH];
    char _pad[7];
} benchmark_vm_config_t;

/* Number of uint64_t results the VMM writes into the shared page. */
#define BENCH_VM_NUM_RESULTS 4

__attribute__((__section__(".benchmark_vm_config"))) benchmark_vm_config_t bench_vm_config;

/* Microkit maps this in, read only for bench and rw for the vmm */
uintptr_t bench_vm_results;

/* VM utilisation only means anything when per-thread tracking is compiled in. */
#if defined(CONFIG_BENCHMARK_TRACK_UTILISATION) && ENABLE_BENCHMARKING
#define BENCH_VM_UTIL 1
#else
#define BENCH_VM_UTIL 0
#endif

typedef struct {
    uint64_t total;
    uint64_t kernel;
    uint64_t schedules;
    uint64_t entries;
} util_sample_t;

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
    static util_sample_t total_sample;
    static util_sample_t child_samples[BENCHMARK_MAX_CHILDREN];
    static util_sample_t vm_sample;

    static uint64_t overflow_status;
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    static uint64_t kernel_log_entries;
#endif


ccnt_t counter_values[8];
counter_bitfield_t benchmark_bf;

serial_queue_handle_t serial_tx_queue_handle;

/**
 * PMU event information fields.
 */
typedef struct {
    const char *event_name; /* Description of the PMU event for result reporting. */
    uint64_t sel4bench_id; /* PMU event identifier - platform specific, but we limit our PMU usage to ARM */
} bench_pmu_event_info_t;

/**
 * PMU event lookup table. Entry i corresponds to bench_pmu_events_t enum value
 * i, see bench.h
 */
bench_pmu_event_info_t pmu_event_table[] = {
    { "L1 i-cache misses", SEL4BENCH_EVENT_CACHE_L1I_MISS },
    { "L1 d-cache misses", SEL4BENCH_EVENT_CACHE_L1D_MISS },
    { "L1 i-tlb misses", SEL4BENCH_EVENT_TLB_L1I_MISS },
    { "L1 d-tlb misses", SEL4BENCH_EVENT_TLB_L1D_MISS },
    { "Instructions", SEL4BENCH_EVENT_EXECUTE_INSTRUCTION },
    { "Branch mispredictions", SEL4BENCH_EVENT_BRANCH_MISPREDICT },
    { "CPU cycles", SEL4BENCH_EVENT_CCNT },
    { "Data memory access", SEL4BENCH_EVENT_MEMORY_ACCESS },
    { "Overflow counter", SEL4BENCH_EVENT_CHAIN },
};

static char *child_name(uint8_t child_id)
{
    for (uint8_t i = 0; i < benchmark_config.num_children; i++) {
        if (child_id == benchmark_config.children[i].child_id) {
            return benchmark_config.children[i].name;
        }
    }
    return "unknown child PD";
}

// Could be moved to a config.h
static bool bench_vm_config_check_magic(void)
{
    for (int i = 0; i < BENCH_VM_MAGIC_LEN; i++) {
        if (bench_vm_config.magic[i] != BENCH_VM_MAGIC[i]) {
            return false;
        }
    }
    return true;
}

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
static void save_util(util_sample_t *s, uint64_t *buf, bool is_total)
{
    if (is_total) {
        s->total     = buf[BENCHMARK_TOTAL_UTILISATION];
        s->kernel    = buf[BENCHMARK_TOTAL_KERNEL_UTILISATION];
        s->schedules = buf[BENCHMARK_TOTAL_NUMBER_SCHEDULES];
        s->entries   = buf[BENCHMARK_TOTAL_NUMBER_KERNEL_ENTRIES];
    } else {
        s->total     = buf[BENCHMARK_TCB_UTILISATION];
        s->kernel    = buf[BENCHMARK_TCB_KERNEL_UTILISATION];
        s->schedules = buf[BENCHMARK_TCB_NUMBER_SCHEDULES];
        s->entries   = buf[BENCHMARK_TCB_NUMBER_KERNEL_ENTRIES];
    }
}

static void print_util_body(util_sample_t *s)
{
    sddf_printf("KernelUtilisation: %lu\nKernelEntries: %lu\nNumberSchedules: "
                "%lu\nTotalUtilisation: %lu\n}\n",
                s->kernel, s->entries, s->schedules, s->total);
}

static void print_total_util(util_sample_t *s)
{
    sddf_printf("Total utilisation details: \n{\n");
    print_util_body(s);
}

static void print_child_util(const char *name, uint8_t id, util_sample_t *s)
{
    sddf_printf("Utilisation details for PD: %s (%u)\n{\n", name, id);
    print_util_body(s);
}

static void print_vm_util(const char *name, uint8_t vcpu_id, util_sample_t *s)
{
    sddf_printf("Utilisation details for VM: %s (vcpu %u)\n{\n", name, vcpu_id);
    print_util_body(s);
}
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
benchmark_track_kernel_entry_t *log_buffer;

static void dump_log_summary(uint64_t log_size)
{
    seL4_Word index = 0;
    seL4_Word syscall_entries = 0;
    seL4_Word fastpaths = 0;
    seL4_Word interrupt_entries = 0;
    seL4_Word userlevelfault_entries = 0;
    seL4_Word vmfault_entries = 0;
    seL4_Word debug_fault = 0;
    seL4_Word other = 0;

    /* log_buffer is never assigned a mapping in this component. Bail out rather
     * than dereference NULL. */
    if (log_buffer == NULL) {
        sddf_printf("BENCH|ERROR: no kernel log buffer mapped, skipping summary\n");
        return;
    }

    while (log_buffer[index].start_time != 0 && index < log_size) {
        if (log_buffer[index].entry.path == Entry_Syscall) {
            if (log_buffer[index].entry.is_fastpath) {
                fastpaths++;
            }
            syscall_entries++;
        } else if (log_buffer[index].entry.path == Entry_Interrupt) {
            interrupt_entries++;
        } else if (log_buffer[index].entry.path == Entry_UserLevelFault) {
            userlevelfault_entries++;
        } else if (log_buffer[index].entry.path == Entry_VMFault) {
            vmfault_entries++;
        } else if (log_buffer[index].entry.path == Entry_DebugFault) {
            debug_fault++;
        } else {
            other++;
        }

        index++;
    }

    sddf_printf("System call invocations %lu", syscall_entries);
    sddf_printf("Fastpaths %lu\n", fastpaths);
    sddf_printf("Interrupt invocations %lu\n", interrupt_entries);
    sddf_printf("User-level faults %lu\n", userlevelfault_entries);
    sddf_printf("VM faults %lu\n", vmfault_entries);
    sddf_printf("Debug faults %lu\n", debug_fault);
    sddf_printf("Others %lu\n", other);
}
#endif

static void benchmark_init(void)
{
#if !ENABLE_BENCHMARKING
    sddf_dprintf("BENCH|LOG: Bench running in debug mode, no access to counters\n");
    return;
#endif

#if ENABLE_PMU_EVENTS
    sel4bench_init();
    seL4_Word n_counters = sel4bench_get_num_counters();
    for (seL4_Word counter = 0; counter < MIN(n_counters, benchmark_config.num_pmu_events); counter++) {
        sel4bench_set_count_event(counter, pmu_event_table[benchmark_config.pmu_events[counter]].sel4bench_id);
        benchmark_bf |= BIT(counter);
    }

    sel4bench_reset_counters();
    sel4bench_start_counters(benchmark_bf);
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    int res_buf = seL4_BenchmarkSetLogBuffer(LOG_BUFFER_CAP);
    if (res_buf) {
        sddf_printf("BENCH|ERROR: Could not set log buffer: %d\n", res_buf);
    } else {
        sddf_printf("BENCH|LOG: Log buffer set\n");
    }
#endif
}

static void benchmark_report(void);

static void benchmark_start(void)
{
#if !ENABLE_BENCHMARKING
    sddf_printf("BENCHMARK: benchmark_start is no-op as benchmarking is disabled\n");
    return;
#endif

#if ENABLE_PMU_EVENTS
    sel4bench_reset_counters();
    /* Reset the overflow status flag register so we can check for overflows to
    32-bit counters during the benchmark */
    PMU_WRITE(PMOVSCLR, 0b111111);
    sel4bench_start_counters(benchmark_bf);
#endif

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
    seL4_BenchmarkResetThreadUtilisation(TCB_CAP);
    for (uint8_t i = 0; i < benchmark_config.num_children; i++) {
        seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + benchmark_config.children[i].child_id);
    }

    // The VMM has control over the VM's TCB and resets it for us
#ifdef BENCH_VM_ENABLED
    microkit_notify(bench_vm_config.ch_start);
#endif

    seL4_BenchmarkResetLog();
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    seL4_BenchmarkResetLog();
#endif

    /* Notify benchmark PD running on next core */
    if (!benchmark_config.last_core) {
        microkit_notify(benchmark_config.tx_start_ch);
    }
}

// Stop all counters. If we are using a vm then we must wait for it to finish,
// otherwise we can report immediately
static void benchmark_stop(void)
{
#if !ENABLE_BENCHMARKING
    sddf_printf("BENCHMARK: benchmark_stop is no-op as benchmarking is disabled\n");
    return;
#endif

#if ENABLE_PMU_EVENTS
    sel4bench_get_counters(benchmark_bf, &counter_values[0]);
    sel4bench_stop_counters(benchmark_bf);
    /* Check the overflow status flag register so we can discard any 32-bit
    counts which have overflowed */
    PMU_READ(PMOVSCLR, overflow_status);
#endif

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
    seL4_BenchmarkFinalizeLog();

    seL4_BenchmarkGetThreadUtilisation(TCB_CAP);
    save_util(&total_sample, (uint64_t *)&seL4_GetIPCBuffer()->msg[0], true);

    for (uint8_t i = 0; i < benchmark_config.num_children; i++) {
        seL4_BenchmarkGetThreadUtilisation(BASE_TCB_CAP + benchmark_config.children[i].child_id);
        save_util(&child_samples[i], (uint64_t *)&seL4_GetIPCBuffer()->msg[0], false);
    }
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    kernel_log_entries = seL4_BenchmarkFinalizeLog();
#endif

#ifdef BENCH_VM_ENABLED
    microkit_notify(bench_vm_config.ch_stop);
#else
    benchmark_report();
#endif
}

static void benchmark_report(void)
{
#if BENCH_VM_ENABLED
    uint64_t *vm = (uint64_t *)(uintptr_t)bench_vm_config.results_vaddr;
    vm_sample.total     = vm[0];
    vm_sample.kernel    = vm[1];
    vm_sample.schedules = vm[2];
    vm_sample.entries   = vm[3];
#endif

    sddf_printf("BENCHMARK: begin output\n");
    sddf_printf("---\n");

#if ENABLE_PMU_EVENTS
    sddf_printf("{CORE %u: \n", benchmark_config.core);
    uint8_t pmu_i = 0;
    while (pmu_i < benchmark_config.num_pmu_events) {
        if (pmu_i + 1 < benchmark_config.num_pmu_events
            && benchmark_config.pmu_events[pmu_i + 1] == CHAIN) {
            sddf_printf("%s: %lu\n", pmu_event_table[benchmark_config.pmu_events[pmu_i]].event_name,
                        counter_values[pmu_i] + (counter_values[pmu_i + 1] << 32));
            pmu_i += 2;
        } else {
            if (overflow_status & 1 << pmu_i) {
                sddf_printf("%s: Overflow occurred during benchmark, event count is invalid!\n",
                            pmu_event_table[benchmark_config.pmu_events[pmu_i]].event_name);
            } else {
                sddf_printf("%s: %lu\n", pmu_event_table[benchmark_config.pmu_events[pmu_i]].event_name,
                            counter_values[pmu_i]);
            }
            pmu_i += 1;
        }
    }
    sddf_printf("}\n");
#endif

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
    print_total_util(&total_sample);
    for (uint8_t i = 0; i < benchmark_config.num_children; i++) {
        print_child_util(benchmark_config.children[i].name,
                         benchmark_config.children[i].child_id,
                         &child_samples[i]);
    }
#if BENCH_VM_ENABLED
        print_vm_util(bench_vm_config.vm_name, bench_vm_config.vcpu_id, &vm_sample);
#endif
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    sddf_printf("KernelEntries:  %lu\n", kernel_log_entries);
    dump_log_summary(kernel_log_entries);
#endif

    sddf_printf("---\n");
    sddf_printf("BENCHMARK: end output\n");

    /* Notify benchmark PD running on next core */
    if (!benchmark_config.last_core) {
        microkit_notify(benchmark_config.tx_stop_ch);
    }
}

void notified(microkit_channel ch)
{
    if (ch == serial_config.tx.id) {
        return;
    } else if (ch == benchmark_config.rx_start_ch) {
        benchmark_start();
    } else if (ch == benchmark_config.rx_stop_ch) {
        benchmark_stop();
#if BENCH_VM_ENABLED
    } else if (ch == bench_vm_config.ch_done) {
        benchmark_report();
#endif
    } else {
        sddf_printf("BENCH|LOG: Bench thread notified on unexpected channel %u\n", ch);
    }
}

void init(void)
{
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

#if BENCH_VM_ENABLED
    sddf_printf("BENCH|LOG: VM utilisation tracking enabled for \"%s\" (vcpu %u)\n",
                bench_vm_config.vm_name, bench_vm_config.vcpu_id);
#endif

#if ENABLE_BENCHMARKING
    sddf_printf("BENCH|LOG: ENABLE_BENCHMARKING defined\n");
#endif
#if ENABLE_PMU_EVENTS
    sddf_printf("BENCH|LOG: ENABLE_PMU_EVENTS defined. Tracking PMU events:\n");
    uint8_t event = 0, i = 0;
    while (i < benchmark_config.num_pmu_events) {
        if (i + 1 < benchmark_config.num_pmu_events && benchmark_config.pmu_events[i + 1] == CHAIN) {
            sddf_printf("%u. %s (64-bit counter)\n", event, pmu_event_table[benchmark_config.pmu_events[i]].event_name);
            i += 2;
        } else {
            sddf_printf("%u. %s (32-bit counter)\n", event, pmu_event_table[benchmark_config.pmu_events[i]].event_name);
            i += 1;
        }
        event++;
    }
#endif
#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
    sddf_printf("BENCH|LOG: CONFIG_BENCHMARK_TRACK_UTILISATION defined\n");
#endif
#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    sddf_printf("BENCH|LOG: CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES defined\n");
#endif

    benchmark_init();
    /* Notify the idle thread that the sel4bench library is initialised. */
    microkit_notify(benchmark_config.init_ch);
}

seL4_Bool fault(microkit_child id, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    sddf_printf("BENCH|LOG: Faulting PD %s (%d)\n", child_name(id), id);

    seL4_UserContext regs;
    seL4_TCB_ReadRegisters(BASE_TCB_CAP + id, false, 0, sizeof(seL4_UserContext) / sizeof(seL4_Word), &regs);
#if defined(CONFIG_ARCH_ARM)
    sddf_printf("Registers: \npc : %lx\nspsr : %lx\nx0 : %lx\nx1 : %lx\nx2 : %lx\nx3 : %lx\nx4 : %lx\nx5 : %lx\nx6 : %lx\nx7 : %lx\n",
                regs.pc, regs.spsr, regs.x0, regs.x1, regs.x2, regs.x3, regs.x4, regs.x5, regs.x6, regs.x7);
#elif defined(CONFIG_ARCH_RISCV)
    sddf_printf("Registers: \npc : %lx\nra : %lx\nsp : %lx\ngp : %lx\ns0 : %lx\ns1 : %lx\ns2 : %lx\ns3 : %lx\ns4 : "
                "%lx\ns5 : %lx\n",
                regs.pc, regs.ra, regs.sp, regs.gp, regs.s0, regs.s1, regs.s2, regs.s3, regs.s4, regs.s5);
#else
    sddf_printf("Register reading not implemented for current ARCH.\n");
#endif

    switch (microkit_msginfo_get_label(msginfo)) {
    case seL4_Fault_CapFault: {
        uint64_t ip = seL4_GetMR(seL4_CapFault_IP);
        uint64_t fault_addr = seL4_GetMR(seL4_CapFault_Addr);
        uint64_t in_recv_phase = seL4_GetMR(seL4_CapFault_InRecvPhase);
        sddf_printf("CapFault: ip=%lx  fault_addr=%lx  in_recv_phase=%s\n", ip, fault_addr,
                    (in_recv_phase == 0 ? "false" : "true"));
        break;
    }
    case seL4_Fault_UserException: {
        sddf_printf("UserException\n");
        break;
    }
    case seL4_Fault_VMFault: {
        uint64_t ip = seL4_GetMR(seL4_VMFault_IP);
        uint64_t fault_addr = seL4_GetMR(seL4_VMFault_Addr);
        uint64_t is_instruction = seL4_GetMR(seL4_VMFault_PrefetchFault);
        uint64_t fsr = seL4_GetMR(seL4_VMFault_FSR);
        sddf_printf("VMFault: ip=%lx  fault_addr=%lx  fsr=%lx %s\n", ip, fault_addr, fsr,
                    (is_instruction ? "(instruction fault)" : "(data fault)"));
        break;
    }
    default:
        sddf_printf("Unknown fault\n");
        break;
    }

    return seL4_False;
}