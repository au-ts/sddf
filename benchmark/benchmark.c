/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>
#include <microkit.h>
#include <sel4/benchmark_track_types.h>
#include <sel4/benchmark_utilisation_types.h>
#include <sddf/benchmark/bench.h>
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

ccnt_t counter_values[8];
counter_bitfield_t benchmark_bf;

serial_queue_handle_t serial_tx_queue_handle;

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
benchmark_track_kernel_entry_t *log_buffer;
#endif

char *counter_names[] = {
    "L1 i-cache misses",
    "L1 d-cache misses",
    "L1 i-tlb misses",
    "L1 d-tlb misses",
    "Instructions",
    "Branch mispredictions",
};

event_id_t benchmarking_events[] = {
    SEL4BENCH_EVENT_CACHE_L1I_MISS,
    SEL4BENCH_EVENT_CACHE_L1D_MISS,
    SEL4BENCH_EVENT_TLB_L1I_MISS,
    SEL4BENCH_EVENT_TLB_L1D_MISS,
    SEL4BENCH_EVENT_EXECUTE_INSTRUCTION,
    SEL4BENCH_EVENT_BRANCH_MISPREDICT,
};

static char *child_name(uint64_t child_id)
{
    for (uint64_t i = 0; i < benchmark_config.num_children; i++) {
        if (child_id == benchmark_config.children[i].child_id) {
            return benchmark_config.children[i].name;
        }
    }
    return "unknown child PD";
}

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
static void microkit_benchmark_start(void)
{
    seL4_BenchmarkResetThreadUtilisation(TCB_CAP);
    for (uint64_t i = 0; i < benchmark_config.num_children; i++) {
        seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + benchmark_config.children[i].child_id);
    }
    seL4_BenchmarkResetLog();
}

static void microkit_benchmark_stop(uint64_t *total, uint64_t *number_schedules, uint64_t *kernel, uint64_t *entries)
{
    seL4_BenchmarkFinalizeLog();
    seL4_BenchmarkGetThreadUtilisation(TCB_CAP);
    uint64_t *buffer = (uint64_t *)&seL4_GetIPCBuffer()->msg[0];

    *total = buffer[BENCHMARK_TOTAL_UTILISATION];
    *number_schedules = buffer[BENCHMARK_TOTAL_NUMBER_SCHEDULES];
    *kernel = buffer[BENCHMARK_TOTAL_KERNEL_UTILISATION];
    *entries = buffer[BENCHMARK_TOTAL_NUMBER_KERNEL_ENTRIES];
}

static void microkit_benchmark_stop_tcb(uint64_t pd_id, uint64_t *total, uint64_t *number_schedules, uint64_t *kernel,
                                        uint64_t *entries)
{
    seL4_BenchmarkGetThreadUtilisation(BASE_TCB_CAP + pd_id);
    uint64_t *buffer = (uint64_t *)&seL4_GetIPCBuffer()->msg[0];

    *total = buffer[BENCHMARK_TCB_UTILISATION];
    *number_schedules = buffer[BENCHMARK_TCB_NUMBER_SCHEDULES];
    *kernel = buffer[BENCHMARK_TCB_KERNEL_UTILISATION];
    *entries = buffer[BENCHMARK_TCB_NUMBER_KERNEL_ENTRIES];
}

static void print_utilisation_details(uint64_t kernel_util, uint64_t kernel_entries, uint64_t number_schedules,
                                      uint64_t total_util)
{
    sddf_printf("{\nKernelUtilisation:  %lx\nKernelEntries:  %lx\nNumberSchedules:  %lx\nTotalUtilisation:  %lx\n}\n",
                kernel_util, kernel_entries, number_schedules, total_util);
}

static void print_total_utilisation_details(uint64_t kernel_util, uint64_t kernel_entries, uint64_t number_schedules,
                                            uint64_t total_util)
{
    sddf_printf("Total utilisation details: \n");
    print_utilisation_details(kernel_util, kernel_entries, number_schedules, total_util);
}

static void print_pd_utilisation_details(uint64_t pd_id, uint64_t kernel_util, uint64_t kernel_entries,
                                         uint64_t number_schedules, uint64_t total_util)
{
    sddf_printf("Utilisation details for PD: %s (%lu)\n", child_name(pd_id), pd_id);
    print_utilisation_details(kernel_util, kernel_entries, number_schedules, total_util);
}
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
static inline void seL4_BenchmarkTrackDumpSummary(benchmark_track_kernel_entry_t *logBuffer, uint64_t logSize)
{
    seL4_Word index = 0;
    seL4_Word syscall_entries = 0;
    seL4_Word fastpaths = 0;
    seL4_Word interrupt_entries = 0;
    seL4_Word userlevelfault_entries = 0;
    seL4_Word vmfault_entries = 0;
    seL4_Word debug_fault = 0;
    seL4_Word other = 0;

    while (logBuffer[index].start_time != 0 && index < logSize) {
        if (logBuffer[index].entry.path == Entry_Syscall) {
            if (logBuffer[index].entry.is_fastpath) {
                fastpaths++;
            }
            syscall_entries++;
        } else if (logBuffer[index].entry.path == Entry_Interrupt) {
            interrupt_entries++;
        } else if (logBuffer[index].entry.path == Entry_UserLevelFault) {
            userlevelfault_entries++;
        } else if (logBuffer[index].entry.path == Entry_VMFault) {
            vmfault_entries++;
        } else if (logBuffer[index].entry.path == Entry_DebugFault) {
            debug_fault++;
        } else {
            other++;
        }

        index++;
    }

    sddf_printf("Number of system call invocations  %llx and fastpaths  %llx\n", syscall_entries, fastpaths);
    sddf_printf("Number of interrupt invocations  %llx\n", interrupt_entries);
    sddf_printf("Number of user-level faults  %llx\n", userlevelfault_entries);
    sddf_printf("Number of VM faults  %llx\n", vmfault_entries);
    sddf_printf("Number of debug faults  %llx\n", debug_fault);
    sddf_printf("Number of others  %llx\n", other);
}
#endif

void notified(microkit_channel ch)
{
    sddf_printf("[benchmark pd]: notified on channel %d, start_ch: %d\n", ch, benchmark_config.start_ch);
    if (ch == serial_config.tx.id) {
        return;
    } else if (ch == benchmark_config.start_ch) {
        sddf_printf("[benchmark pd]: start ch\n");
        /* sddf_printf("[benchmark pd]: start ch, %d, %d, %d, %d\n", */
                    /* BENCHMARK_TCB_UTILISATION, */
                    /* BENCHMARK_TCB_NUMBER_SCHEDULES, */
                    /* BENCHMARK_TCB_KERNEL_UTILISATION, */
                    /* BENCHMARK_TCB_NUMBER_KERNEL_ENTRIES); */
#ifdef MICROKIT_CONFIG_benchmark

        sel4bench_reset_counters();
        THREAD_MEMORY_RELEASE();
        sel4bench_start_counters(benchmark_bf);

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
        sddf_printf("start benchmark\n");
        microkit_benchmark_start();
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
        seL4_BenchmarkResetLog();
#endif
#endif
    } else if (ch == benchmark_config.stop_ch) {
#ifdef MICROKIT_CONFIG_benchmark
        sel4bench_get_counters(benchmark_bf, &counter_values[0]);
        sel4bench_stop_counters(benchmark_bf);

        sddf_printf("{\n");
        for (int i = 0; i < ARRAY_SIZE(benchmarking_events); i++) {
            sddf_printf("%s: %lX\n", counter_names[i], counter_values[i]);
        }
        sddf_printf("}\n");
#endif

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
        uint64_t total;
        uint64_t kernel;
        uint64_t entries;
        uint64_t number_schedules;
        microkit_benchmark_stop(&total, &number_schedules, &kernel, &entries);
        print_total_utilisation_details(kernel, entries, number_schedules, total);
        for (uint8_t i = 0; i < benchmark_config.num_children; i++) {
            uint8_t child_id = benchmark_config.children[i].child_id;
            sddf_printf("stop benchmark\n");
            microkit_benchmark_stop_tcb(child_id, &total, &number_schedules, &kernel, &entries);
            print_pd_utilisation_details(child_id, kernel, entries, number_schedules, total);
        }
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
        entries = seL4_BenchmarkFinalizeLog();
        sddf_printf("KernelEntries:  %llx\n", entries);
        seL4_BenchmarkTrackDumpSummary(log_buffer, entries);
#endif
    } else {
        sddf_printf("Bench thread notified on unexpected channel\n");
    }
}

void init(void)
{
    serial_queue_init(&serial_tx_queue_handle, serial_config.tx.queue.vaddr, serial_config.tx.data.size,
                      serial_config.tx.data.vaddr);
    serial_putchar_init(serial_config.tx.id, &serial_tx_queue_handle);

#ifdef MICROKIT_CONFIG_benchmark
    sddf_printf("MICROKIT_CONFIG_benchmark defined\n");
#endif
#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
    sddf_printf("CONFIG_BENCHMARK_TRACK_UTILISATION defined\n");
#endif
#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    sddf_printf("CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES defined\n");
#endif

#ifdef MICROKIT_CONFIG_benchmark
    sel4bench_init();
    seL4_Word n_counters = sel4bench_get_num_counters();

    counter_bitfield_t mask = 0;

    for (seL4_Word counter = 0; counter < n_counters; counter++) {
        if (counter >= ARRAY_SIZE(benchmarking_events)) {
            break;
        }
        sel4bench_set_count_event(counter, benchmarking_events[counter]);
        mask |= BIT(counter);
    }

    sel4bench_reset_counters();
    sel4bench_start_counters(mask);
    benchmark_bf = mask;
#else
    sddf_dprintf("BENCH|LOG: Bench running in debug mode, no access to counters\n");
#endif

    /* Notify the idle thread that the sel4bench library is initialised. */
    microkit_notify(benchmark_config.init_ch);

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    int res_buf = seL4_BenchmarkSetLogBuffer(LOG_BUFFER_CAP);
    if (res_buf) {
        sddf_printf("Could not set log buffer:  %llx\n", res_buf);
    } else {
        sddf_printf("Log buffer set\n");
    }
#endif
    sddf_printf("Benchmark is ready\n");
}

seL4_Bool fault(microkit_child id, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    sddf_printf("BENCH|LOG: Faulting PD %s (%d)\n", child_name(id), id);

    seL4_UserContext regs;
    seL4_TCB_ReadRegisters(BASE_TCB_CAP + id, false, 0, sizeof(seL4_UserContext) / sizeof(seL4_Word), &regs);
    sddf_printf("Registers: \npc : %lx\nspsr : %lx\nx0 : %lx\nx1 : %lx\nx2 : %lx\nx3 : %lx\nx4 : %lx\nx5 : %lx\nx6 : %lx\nx7 : %lx\n",
                regs.pc, regs.spsr, regs.x0, regs.x1, regs.x2, regs.x3, regs.x4, regs.x5, regs.x6, regs.x7);

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
