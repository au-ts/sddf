/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

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
/* headers only for benchmarking constants */
#include <sddf/blk/queue.h>
#include <benchmark_config.h>
#include <sddf/timer/client.h>

#define LOG_BUFFER_CAP 7


/* Notification channels and TCB CAP offsets - ensure these align with .system file! */
#define SERIAL_TX_CH 0
#define START 1
#define STOP 2
#define BENCH_RUN_CH 3
#define TIMER_CH 4
#define IDLE_INIT_CH 5
// ID's of protection domains (must align with the system description file
#define PD_TOTAL        0
#define PD_BLK_ID       1
#define PD_VIRT_ID      2
#define PD_CLIENT_ID    3
#define PD_UART_ID      4
#define PD_UART_VIRT_ID 5
#define PD_IDLE_ID      6
#define PD_TIMER_ID     7

// Human-readable names of the PDs XXX for ethernet bench this is in ethernet_config.h
#define BLK_DRIVER_NAME "blk_driver"
#define BLK_VIRTUALISER_NAME "virt"
#define BLK_CLIENT_NAME "client0"
#define BLK_UART_NAME "uart"
#define BLK_UART_VIRT_NAME "virt_uart"
#define BLK_IDLE_NAME "idle"
#define BLK_TIMER_NAME "timer"

uintptr_t uart_base;
uintptr_t cyclecounters_vaddr;

ccnt_t counter_values[8];
counter_bitfield_t benchmark_bf;
// benchmark run tracking vars
ccnt_t ccounter_benchmark_start;
ccnt_t ccounter_benchmark_stop;
uint64_t timer_start;
uint64_t timer_end;
uint64_t timeout_uart = 6e9;
uint8_t benchmark_size_idx = 0;

char *serial_tx_data;
serial_queue_t *serial_tx_queue;
serial_queue_handle_t serial_tx_queue_handle;
bool printing_results_timeout = false;

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
benchmark_track_kernel_entry_t *log_buffer;
#endif

void panic(char* reason) {
    sddf_printf("BENCH | Panic! %s\n", reason);
    __builtin_trap();
}

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

typedef struct benchmark_run_resuls {
    /* throughput values computed using timer driver and cycle count + CPU freq */
    double speed;
    double speed_ccount;
    /* time measured with timer driver and based on cycle_count + CPU freq */
    uint64_t time;
    uint64_t time_ccount;
    /* cpu util computed as (cycles from Client, block driver, virtualiser) / total cycles */
    float cpuutil;
    /* context switches per PD */
    uint64_t no_schedules_driver;
    uint64_t no_schedules_virtualiser;
    uint64_t no_schedules_client;
    uint64_t no_schedules_idle;
    /* cycles per PD */
    uint64_t cycles_driver;
    uint64_t cycles_virtualiser;
    uint64_t cycles_client;
    uint64_t cycles_idle;
} benchmark_run_resuls_t;

benchmark_run_resuls_t benchmark_run_results_rand_read[BENCHMARK_RUN_COUNT*BENCHMARK_INDIVIDUAL_RUN_REPEATS];
benchmark_run_resuls_t benchmark_run_results_rand_write[BENCHMARK_RUN_COUNT*BENCHMARK_INDIVIDUAL_RUN_REPEATS];
benchmark_run_resuls_t benchmark_run_results_seq_read[BENCHMARK_RUN_COUNT*BENCHMARK_INDIVIDUAL_RUN_REPEATS];
benchmark_run_resuls_t benchmark_run_results_seq_write[BENCHMARK_RUN_COUNT*BENCHMARK_INDIVIDUAL_RUN_REPEATS];

enum run_benchmark_state run_benchmark_state = THROUGHPUT_RANDOM_READ;
int benchmark_run_idx = 0;

static void print_pdid_name(uint64_t pd_id) {
    switch (pd_id) {
    case PD_BLK_ID:
        sddf_printf(BLK_DRIVER_NAME);
        break;
    case PD_VIRT_ID:
        sddf_printf(BLK_VIRTUALISER_NAME);
        break;
    case PD_CLIENT_ID:
        sddf_printf(BLK_CLIENT_NAME);
        break;
    case PD_UART_ID:
        sddf_printf(BLK_UART_NAME);
        break;
    case PD_UART_VIRT_ID:
        sddf_printf(BLK_UART_VIRT_NAME);
        break;
    case PD_IDLE_ID:
        sddf_printf(BLK_IDLE_NAME);
        break;
    case PD_TIMER_ID:
        sddf_printf(BLK_TIMER_NAME);
        break;
    default:
        sddf_printf("unknown");
        break;
    }
}

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
static void microkit_benchmark_start(void) {
    seL4_BenchmarkResetThreadUtilisation(TCB_CAP);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_BLK_ID);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_VIRT_ID);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_CLIENT_ID);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_UART_ID);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_UART_VIRT_ID);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_IDLE_ID);
    seL4_BenchmarkResetThreadUtilisation(BASE_TCB_CAP + PD_TIMER_ID);
    seL4_BenchmarkResetLog();
}

static void microkit_benchmark_stop(uint64_t *total, uint64_t *number_schedules, uint64_t *kernel, uint64_t *entries) {
    seL4_BenchmarkFinalizeLog();
    seL4_BenchmarkGetThreadUtilisation(TCB_CAP);
    uint64_t *buffer = (uint64_t *)&seL4_GetIPCBuffer()->msg[0];

    *total = buffer[BENCHMARK_TOTAL_UTILISATION];
    *number_schedules = buffer[BENCHMARK_TOTAL_NUMBER_SCHEDULES];
    *kernel = buffer[BENCHMARK_TOTAL_KERNEL_UTILISATION];
    *entries = buffer[BENCHMARK_TOTAL_NUMBER_KERNEL_ENTRIES];
}

static void microkit_benchmark_stop_tcb(uint64_t pd_id, uint64_t *total, uint64_t *number_schedules, uint64_t *kernel,
                                        uint64_t *entries) {
    seL4_BenchmarkGetThreadUtilisation(BASE_TCB_CAP + pd_id);
    uint64_t *buffer = (uint64_t *)&seL4_GetIPCBuffer()->msg[0];

    *total = buffer[BENCHMARK_TCB_UTILISATION];
    *number_schedules = buffer[BENCHMARK_TCB_NUMBER_SCHEDULES];
    *kernel = buffer[BENCHMARK_TCB_KERNEL_UTILISATION];
    *entries = buffer[BENCHMARK_TCB_NUMBER_KERNEL_ENTRIES];
}

static void print_benchmark_details(uint64_t pd_id, uint64_t kernel_util, uint64_t kernel_entries,
                                    uint64_t number_schedules, uint64_t total_util) {
//    if (pd_id == PD_TOTAL) {
//        sddf_printf("Total utilisation details: \n");
//    } else {
//        sddf_printf("Utilisation details for PD: ");
//        print_pdid_name(pd_id);
//        sddf_printf(" (%lx)\n", pd_id);
//    }
//    sddf_printf("{\nKernelUtilisation:  %lx\nKernelEntries:  %lx\nNumberSchedules:  %lx\nTotalUtilisation:  %lx\n}\n",
//                kernel_util, kernel_entries, number_schedules, total_util);
}
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
static inline void seL4_BenchmarkTrackDumpSummary(benchmark_track_kernel_entry_t *logBuffer, uint64_t logSize) {
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

void print_benchmark_results_for_state(enum run_benchmark_state print_state) {
    benchmark_run_resuls_t* bench_results;
    const char* run_name = human_readable_run_benchmark_state[print_state];
    switch (print_state) {
        case THROUGHPUT_RANDOM_READ:
            bench_results = benchmark_run_results_rand_read;
            break;
        case THROUGHPUT_RANDOM_WRITE:
            bench_results = benchmark_run_results_rand_write;
            break;
        case THROUGHPUT_SEQUENTIAL_READ:
            bench_results = benchmark_run_results_seq_read;
            break;
        case THROUGHPUT_SEQUENTIAL_WRITE:
            bench_results = benchmark_run_results_seq_write;
            break;
        default:
            panic("BENCHMARK: Error, unimplemented benchmark state transition");
    }
    sddf_printf("%s results:\n", run_name);
    for (int j = 0; j != BENCHMARK_INDIVIDUAL_RUN_REPEATS; ++j) {
        sddf_printf("Run idx: %d/%d\n", j+1, BENCHMARK_INDIVIDUAL_RUN_REPEATS);
        for (int i = 0; i != BENCHMARK_RUN_COUNT; ++i) {
            sddf_printf("No. rqs: %d, rq size: 0x%x B, speed: %.2f MiB/s,"
                    " speed_ccount: %.2f MiB/s, time: %lu ms, time_ccount: %lu ms, cpu_util: %.2f perc, "
                    "cyc_driv: 0x%lx, cyc_virt: 0x%lx, cyc_cli: 0x%lx, cyc_idle: 0x%lx\n",
                    REQUEST_COUNT[i],
                    BENCHMARK_BLOCKS_PER_REQUEST[i] * BLK_TRANSFER_SIZE,
                    bench_results[i + j*BENCHMARK_RUN_COUNT].speed,
                    bench_results[i + j*BENCHMARK_RUN_COUNT].speed_ccount,
                    (unsigned long) (bench_results[i + j*BENCHMARK_RUN_COUNT].time/1e6),
                    (unsigned long) (bench_results[i + j*BENCHMARK_RUN_COUNT].time_ccount/1e6),
                    bench_results[i + j*BENCHMARK_RUN_COUNT].cpuutil,
                    bench_results[i + j*BENCHMARK_RUN_COUNT].cycles_driver,
                    bench_results[i + j*BENCHMARK_RUN_COUNT].cycles_virtualiser,
                    bench_results[i + j*BENCHMARK_RUN_COUNT].cycles_client,
                    bench_results[i + j*BENCHMARK_RUN_COUNT].cycles_idle);
        }
    }
}

void print_all_benchmark_results() {
    /*
     * Splits printing full results in half, adding a 6 second timeout in the middle,
     * to allow the uart driver to catch up. Timeout added, as increasing memory region for the uart driver
     * no longer solved uart hanging/garbling the output.
     */
    if (!printing_results_timeout) {
        print_benchmark_results_for_state(THROUGHPUT_RANDOM_READ);
        print_benchmark_results_for_state(THROUGHPUT_RANDOM_WRITE);
        printing_results_timeout = true;
        sddf_timer_set_timeout(TIMER_CH, 6e9);
    } else {
        printing_results_timeout = false;
        print_benchmark_results_for_state(THROUGHPUT_SEQUENTIAL_READ);
        print_benchmark_results_for_state(THROUGHPUT_SEQUENTIAL_WRITE);
    }
}

void notified(microkit_channel ch) {
    switch (ch) {
    case TIMER_CH:
        if (printing_results_timeout) {
            /* All benchmark results printed flood the uart, split in half so timing out after first half */
            print_all_benchmark_results();
        } else {
            /* Timeout for UART to flush complete, run next benchmark */
            microkit_notify(BENCH_RUN_CH);
        }
        break;
    case START:
#if defined(MICROKIT_CONFIG_benchmark) && !defined(VALIDATE_IO_OPERATIONS)
        /* sample the clock cycles, to later get a total amount of cycles spent during a benchmark */
        ccounter_benchmark_start = sel4bench_get_cycle_count();
        timer_start = sddf_timer_time_now(TIMER_CH);
        sel4bench_reset_counters();
        THREAD_MEMORY_RELEASE();
        sel4bench_start_counters(benchmark_bf);

#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
        microkit_benchmark_start();
#endif

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
        seL4_BenchmarkResetLog();
#endif
#endif
        break;
    case STOP:
#if defined(MICROKIT_CONFIG_benchmark) && !defined(VALIDATE_IO_OPERATIONS)
        timer_end = sddf_timer_time_now(TIMER_CH);
        ccounter_benchmark_stop = sel4bench_get_cycle_count();
        sel4bench_get_counters(benchmark_bf, &counter_values[0]);
        sel4bench_stop_counters(benchmark_bf);
        uint64_t cycles_PD_TOTAL = 0;
        uint64_t cycles_PD_BLK_VIRT_CLI = 0;
        uint64_t cycles_summed = 0;
        int run_offset = benchmark_run_idx * BENCHMARK_RUN_COUNT;
        benchmark_run_resuls_t* bench_results;
        switch (run_benchmark_state) {
            case THROUGHPUT_RANDOM_READ:
                bench_results = benchmark_run_results_rand_read;
                break;
            case THROUGHPUT_RANDOM_WRITE:
                bench_results = benchmark_run_results_rand_write;
                break;
            case THROUGHPUT_SEQUENTIAL_READ:
                bench_results = benchmark_run_results_seq_read;
                break;
            case THROUGHPUT_SEQUENTIAL_WRITE:
                bench_results = benchmark_run_results_seq_write;
                break;
            default:
                panic("BENCHMARK: Error, unimplemented benchmark state transition");
        }
#ifdef CONFIG_BENCHMARK_TRACK_UTILISATION
        uint64_t total;
        uint64_t kernel;
        uint64_t entries;
        uint64_t number_schedules;
        microkit_benchmark_stop(&total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_TOTAL, kernel, entries, number_schedules, total);
        cycles_PD_TOTAL = total;

        microkit_benchmark_stop_tcb(PD_BLK_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_BLK_ID, kernel, entries, number_schedules, total);
        cycles_PD_BLK_VIRT_CLI += total;
        cycles_summed += total;
        bench_results[benchmark_size_idx + run_offset].no_schedules_driver = number_schedules;
        bench_results[benchmark_size_idx + run_offset].cycles_driver = total;

        microkit_benchmark_stop_tcb(PD_VIRT_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_VIRT_ID, kernel, entries, number_schedules, total);
        cycles_PD_BLK_VIRT_CLI += total;
        cycles_summed += total;
        bench_results[benchmark_size_idx + run_offset].no_schedules_virtualiser = number_schedules;
        bench_results[benchmark_size_idx + run_offset].cycles_virtualiser = total;

        microkit_benchmark_stop_tcb(PD_CLIENT_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_CLIENT_ID, kernel, entries, number_schedules, total);
        cycles_PD_BLK_VIRT_CLI += total;
        cycles_summed += total;
        bench_results[benchmark_size_idx + run_offset].no_schedules_client = number_schedules;
        bench_results[benchmark_size_idx + run_offset].cycles_client = total;

        microkit_benchmark_stop_tcb(PD_UART_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_UART_ID, kernel, entries, number_schedules, total);
        cycles_summed += total;

        microkit_benchmark_stop_tcb(PD_UART_VIRT_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_UART_VIRT_ID, kernel, entries, number_schedules, total);
        cycles_summed += total;

        microkit_benchmark_stop_tcb(PD_IDLE_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_IDLE_ID, kernel, entries, number_schedules, total);
        cycles_summed += total;
        bench_results[benchmark_size_idx + run_offset].no_schedules_idle = number_schedules;
        bench_results[benchmark_size_idx + run_offset].cycles_idle = total;

        microkit_benchmark_stop_tcb(PD_TIMER_ID, &total, &number_schedules, &kernel, &entries);
        print_benchmark_details(PD_TIMER_ID, kernel, entries, number_schedules, total);
        cycles_summed += total;
#endif

        //sddf_printf("{\n");
        //for (int i = 0; i < ARRAY_SIZE(benchmarking_events); i++) {
        //    sddf_printf("%s: %lX\n", counter_names[i], counter_values[i]);
        //}
        /* Get the total cycle count spent during benchmark, compute cycles/KiB */
        uint64_t elapsed_time = timer_end-timer_start;
        //sddf_printf("Total time (ns): %ld\n", elapsed_time);
        double speed = ((double) BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx] * BLK_TRANSFER_SIZE * \
                REQUEST_COUNT[benchmark_size_idx] / (1024. * 1024.)) / ((double) (elapsed_time)*1e-9);
        //sddf_printf("speed (MiB/s: %f\n", speed);
        float cpuutil = (float) (((double) cycles_PD_BLK_VIRT_CLI /  cycles_PD_TOTAL) * 100);
        //sddf_printf("old cpuutil: %f\n", cpuutil);
        cpuutil = (float) (((double) (cycles_PD_TOTAL - bench_results[benchmark_size_idx + run_offset].cycles_idle) /  cycles_PD_TOTAL) * 100);
        //sddf_printf("new cpuutil: %f\n", cpuutil);
        /* compute MiB/s based on cyclecount (NOTE: using hardcoded CPU freq, as per uboot) */
#ifdef MICROKIT_BOARD_odroidc4
        /* formula: amount of data transferred / (cycles_PD_TOTAL / ODROID_CPU_CLKFREQ_MHZ) */
        uint64_t elapsed_time_ccount = (uint64_t) (cycles_PD_TOTAL / (ODROID_CPU_CLKFREQ_MHZ) * 1e3);
        double speed_ccount = ((double) BENCHMARK_BLOCKS_PER_REQUEST[benchmark_size_idx] * BLK_TRANSFER_SIZE * \
                REQUEST_COUNT[benchmark_size_idx] / (1024. * 1024.)) / \
                (elapsed_time_ccount *1e-9);
#else
        double speed_ccount = 0.; 
        uint64_t elapsed_time_ccount = 0;
#endif
        bench_results[benchmark_size_idx + run_offset].speed = speed;
        bench_results[benchmark_size_idx + run_offset].speed_ccount = speed_ccount;
        bench_results[benchmark_size_idx + run_offset].time = elapsed_time;
        bench_results[benchmark_size_idx + run_offset].time_ccount = elapsed_time_ccount;
        bench_results[benchmark_size_idx + run_offset].cpuutil = cpuutil;

        //sddf_printf("total cycles: 0x%lx\n", ccounter_benchmark_stop-ccounter_benchmark_start);
        //sddf_printf("PMU measured total: 0x%lx, PMU measured sum rest: 0x%lx, diff: 0x%lx\n", cycles_PD_TOTAL, cycles_summed, cycles_PD_TOTAL-cycles_summed);
        //sddf_printf("}\n");

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
        entries = seL4_BenchmarkFinalizeLog();
        sddf_printf("KernelEntries:  %llx\n", entries);
        seL4_BenchmarkTrackDumpSummary(log_buffer, entries);
#endif
        benchmark_size_idx = benchmark_size_idx + 1;
        // Print out results:
        switch (run_benchmark_state) {
            case THROUGHPUT_RANDOM_READ:
                print_benchmark_results_for_state(THROUGHPUT_RANDOM_READ);
                break;
            case THROUGHPUT_RANDOM_WRITE:
                //print_benchmark_results_for_state(THROUGHPUT_RANDOM_READ);
                print_benchmark_results_for_state(THROUGHPUT_RANDOM_WRITE);
                break;
            case THROUGHPUT_SEQUENTIAL_READ:
                //print_benchmark_results_for_state(THROUGHPUT_RANDOM_READ);
                //print_benchmark_results_for_state(THROUGHPUT_RANDOM_WRITE);
                print_benchmark_results_for_state(THROUGHPUT_SEQUENTIAL_READ);
                break;
            case THROUGHPUT_SEQUENTIAL_WRITE:
                // XXX: only for the last run repeat of sequential write, print ALL results
                if (benchmark_size_idx % BENCHMARK_RUN_COUNT == 0 && \
                        (benchmark_run_idx + 1) % BENCHMARK_INDIVIDUAL_RUN_REPEATS == 0) {
                    sddf_printf("BENCH|Finished all Benchmarks, printing all results!\n");
                    print_all_benchmark_results();
                } else {
                    print_benchmark_results_for_state(THROUGHPUT_SEQUENTIAL_WRITE);
                }
                break;
            default:
                panic("BENCHMARK: Error, unimplemented benchmark state transition");
        }
        benchmark_size_idx %= BENCHMARK_RUN_COUNT;
        if (benchmark_size_idx == 0) {
            benchmark_run_idx = (benchmark_run_idx + 1) % BENCHMARK_INDIVIDUAL_RUN_REPEATS;
            if (benchmark_run_idx == 0)
                switch (run_benchmark_state) {
                    case THROUGHPUT_RANDOM_READ:
                        run_benchmark_state = THROUGHPUT_RANDOM_WRITE;
                        break;
                    case THROUGHPUT_RANDOM_WRITE:
                        run_benchmark_state = THROUGHPUT_SEQUENTIAL_READ;
                        break;
                    case THROUGHPUT_SEQUENTIAL_READ:
                        run_benchmark_state = THROUGHPUT_SEQUENTIAL_WRITE;
                        break;
                    case THROUGHPUT_SEQUENTIAL_WRITE:
                        run_benchmark_state = LATENCY_READ;
                        break;
                    default:
                        panic("BENCHMARK: Error, unimplemented benchmark state transition");
                }
        }
#endif

        /* spin to let UART flush its content */
        sddf_printf("benchmark: wait for UART to print out its msgs. Timing out for: %f ms.\n", timeout_uart/1e6);
        sddf_timer_set_timeout(TIMER_CH, timeout_uart);
        break;
    case SERIAL_TX_CH:
        // Nothing to do
        break;
    default:
        sddf_printf("Bench thread notified on unexpected channel\n");
    }
}

void init(void) {
    serial_cli_queue_init_sys(microkit_name, NULL, NULL, NULL, &serial_tx_queue_handle, serial_tx_queue, serial_tx_data);
    serial_putchar_init(SERIAL_TX_CH, &serial_tx_queue_handle);
    sddf_printf("BENCH| LOG Bench thread init!\n");
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
    microkit_notify(IDLE_INIT_CH);
    /* Notify the client to start the benchmark run */
    microkit_notify(BENCH_RUN_CH);

#ifdef CONFIG_BENCHMARK_TRACK_KERNEL_ENTRIES
    int res_buf = seL4_BenchmarkSetLogBuffer(LOG_BUFFER_CAP);
    if (res_buf) {
        sddf_printf("Could not set log buffer:  %llx\n", res_buf);
    } else {
        sddf_printf("Log buffer set\n");
    }
#endif
}

seL4_Bool fault(microkit_child id, microkit_msginfo msginfo, microkit_msginfo *reply_msginfo) {
    sddf_printf("BENCH|LOG: Faulting PD ");
    print_pdid_name(id);
    sddf_printf(" (%x)\n", id);

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
