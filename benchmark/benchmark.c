/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdbool.h>
#include <stdint.h>
#include <microkit.h>
#include <sel4/benchmark_track_types.h>
#include <sel4/benchmark_utilisation_types.h>
#include <sddf/benchmark/bench.h>
#include <sddf/benchmark/sel4bench.h>
#include <sddf/serial/queue.h>
#include <sddf/util/fence.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>
#include <serial_config.h>
#include <ethernet_config.h>
#include <core_config.h>

#define SERIAL_TX_CH 0

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;

#define LOG_BUFFER_CAP 7

/* Channel START signal is received on. */
#define RX_START 1

/* Channel STOP signal is received on. */
#define RX_STOP 2

/* Channel to transmit START signal. */
#define TX_START 3

/* Channel to transmit STOP signal. */
#define TX_STOP 4

/* Channel to initialise idle thread. */
#define IDLE_INIT 5

/* Identifier used to track utilisation for entire core. */
#define TOTAL_ID 0

core_config_t core_config;

ccnt_t counter_values[8];
counter_bitfield_t benchmark_bf;

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

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
static void benchmark_start_core()
{
    seL4_BenchmarkResetThreadUtilisation(TCB_CAP);
    for (uint32_t id = 1; id < core_config.max_core_id + 1; id++) {
        if (core_config.core_bitmap & (1 << id)) {
            seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + id);
        }
    }
    seL4_BenchmarkResetLog();
}

static void benchmark_print_IPC_data(uint64_t *buffer, uint32_t id)
{
    uint64_t total, number_schedules, kernel, entries;
    if (id == TOTAL_ID) {
        total = buffer[BENCHMARK_TOTAL_UTILISATION];
        number_schedules = buffer[BENCHMARK_TOTAL_NUMBER_SCHEDULES];
        kernel = buffer[BENCHMARK_TOTAL_KERNEL_UTILISATION];
        entries = buffer[BENCHMARK_TOTAL_NUMBER_KERNEL_ENTRIES];
        sddf_printf("Total utilisation details: \n");
    } else {
        total = buffer[BENCHMARK_TCB_UTILISATION];
        number_schedules = buffer[BENCHMARK_TCB_NUMBER_SCHEDULES];
        kernel = buffer[BENCHMARK_TCB_KERNEL_UTILISATION];
        entries = buffer[BENCHMARK_TCB_NUMBER_KERNEL_ENTRIES];
        sddf_printf("Utilisation details for PD: %s (%x)\n", pd_id_to_name(id), id);
    }
    sddf_printf("{\nKernelUtilisation: %lx\nKernelEntries: "
                "%lx\nNumberSchedules: %lx\nTotalUtilisation: %lx\n}\n",
                kernel, entries, number_schedules, total);
}

static void benchmark_stop_core()
{
    seL4_BenchmarkFinalizeLog();
    seL4_BenchmarkGetThreadUtilisation(TCB_CAP);
    benchmark_print_IPC_data((uint64_t *)&seL4_GetIPCBuffer()->msg[0], TOTAL_ID);
    for (uint32_t id = 1; id < core_config.max_core_id + 1; id++) {
        if (core_config.core_bitmap & (1 << id)) {
            seL4_BenchmarkGetThreadUtilisation(BASE_TCB_CAP + id);
            benchmark_print_IPC_data((uint64_t *)&seL4_GetIPCBuffer()->msg[0], id);
        }
    }
}
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
benchmark_track_kernel_entry_t *log_buffer;

static inline void seL4_BenchmarkTrackDumpSummary(uint64_t logSize)
{
    seL4_Word index = 0;
    seL4_Word syscall_entries = 0;
    seL4_Word fastpaths = 0;
    seL4_Word interrupt_entries = 0;
    seL4_Word userlevelfault_entries = 0;
    seL4_Word vmfault_entries = 0;
    seL4_Word debug_fault = 0;
    seL4_Word other = 0;

    while (log_buffer[index].start_time != 0 && index < logSize) {
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

    sddf_printf("System call invocations %lx", syscall_entries);
    sddf_printf("Fastpaths %lx\n", fastpaths);
    sddf_printf("Interrupt invocations %lx\n", interrupt_entries);
    sddf_printf("User-level faults %lx\n", userlevelfault_entries);
    sddf_printf("VM faults %lx\n", vmfault_entries);
    sddf_printf("Debug faults %lx\n", debug_fault);
    sddf_printf("Others %lx\n", other);
}
#endif


void notified(microkit_channel ch)
{
    switch (ch) {
    case RX_START:
#ifdef MICROKIT_CONFIG_benchmark
        sel4bench_reset_counters();
        THREAD_MEMORY_RELEASE();
        sel4bench_start_counters(benchmark_bf);

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
        benchmark_start_core();
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
        seL4_BenchmarkResetLog();
#endif
#endif
        if (!core_config.last_core)
            microkit_notify(TX_START);
        break;

    case RX_STOP:
#ifdef MICROKIT_CONFIG_benchmark
        sel4bench_get_counters(benchmark_bf, &counter_values[0]);
        sel4bench_stop_counters(benchmark_bf);

        sddf_printf("{CORE %u: \n", core_config.core_value);
        for (int i = 0; i < ARRAY_SIZE(benchmarking_events); i++) {
            sddf_printf("%s: %lX\n", counter_names[i], counter_values[i]);
        }
        sddf_printf("}\n");
#endif

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
        benchmark_stop_core();
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
        uint64_t log_size = seL4_BenchmarkFinalizeLog();
        sddf_printf("KernelEntries:  %lx\n", log_size);
        seL4_BenchmarkTrackDumpSummary(log_size);
#endif
        THREAD_MEMORY_RELEASE();
        if (!core_config.last_core)
            microkit_notify(TX_STOP);
        break;

    case SERIAL_TX_CH:
        // Nothing to do
        break;

    default:
        sddf_printf("BENCH|LOG: Bench thread notified on unexpected channel\n");
    }
}

void init(void)
{
    uint32_t serial_tx_data_capacity;
    serial_cli_data_capacity(microkit_name, NULL, &serial_tx_data_capacity);
    serial_queue_init(&serial_tx_queue_handle, serial_tx_queue, serial_tx_data_capacity, serial_tx_data);
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);

    bench_core_config_info(microkit_name, &core_config);

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

    microkit_notify(IDLE_INIT);

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    int res_buf = seL4_BenchmarkSetLogBuffer(LOG_BUFFER_CAP);
    if (res_buf) {
        sddf_printf("BENCH|ERROR: Could not set log buffer: %d\n", res_buf);
    } else {
        sddf_printf("BENCH|LOG: Log buffer set\n");
    }
#endif
}

seL4_Bool fault(microkit_child id, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo)
{
    sddf_printf("BENCH|LOG: Faulting PD %s (%x)\n", pd_id_to_name(id), id);

    seL4_UserContext regs;
    seL4_TCB_ReadRegisters(BASE_TCB_CAP + id, false, 0, sizeof(seL4_UserContext) / sizeof(seL4_Word), &regs);
    sddf_printf("Registers: \npc : %lx\nspsr : %lx\nx0 : %lx\nx1 : %lx\n"
                "x2 : %lx\nx3 : %lx\nx4 : %lx\nx5 : %lx\nx6 : %lx\nx7 : %lx\n",
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
