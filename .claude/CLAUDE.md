# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What This Project Is

**seL4 Device Driver Framework (sDDF)** — a research framework from UNSW Sydney for writing device drivers as isolated seL4 user-level protection domains. Components communicate via shared-memory queues and asynchronous notifications (microkit_notify), never via direct calls. The active work on this branch (`luke-iperf3-client`) is an iperf3 client in `examples/iperf3_udp/` and `examples/iperf3/`.

## Build and Run

```sh
# Clean build
make clean MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0

# Build
make MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0
```

Before running QEMU, start an iperf3 server in another shell on the expected port (default 5202):
```sh
iperf3 -s -p 5202
```

The build produces `build/loader.img`. Run it with the `qemu` make target.

## Architecture

### Component Model

Each protection domain is a separate ELF compiled from its own `.c` files. The system is composed via a Python metaprogram (`meta.py`) that generates a Microkit System Description File (SDF). Configuration is injected into each ELF at link time via linker sections (e.g., `__attribute__((__section__(".net_client_config"))) net_client_config_t net_config`).

### Network Stack

```
Ethernet Driver  →  virt_tx / virt_rx  →  (copy component, optional)  →  lwIP  →  App
```

- Drivers live in `drivers/network/<driver>/`
- Virtualisation (`network/components/virt_rx.c`, `virt_tx.c`) multiplexes between clients
- lwIP is integrated via `network/lib_sddf_lwip/` which bridges sDDF queues to the lwIP netif
- Apps include `<sddf/network/lib_sddf_lwip.h>` and interact purely through lwIP APIs

### iperf3 Structure

```
iperf3_client.c   — init, lwIP tick, DHCP, entry points, notified() dispatch
iperf3_ctrl.c     — TCP control connection state machine (param exchange, CREATE_STREAMS, TEST_START, etc.)
iperf3_ctrl.h     — shared types: iperf_ctrl_t, test states
iperf3_stream.c   — TCP stream tx helper + UDP stream pump (udp_pump)
iperf3_stream.h   — iperf3_stream_t (TCP) and iperf3_udp_stream_t (UDP)
```

Config is hardcoded: server 10.0.2.2:5202, 5-second duration, 1 stream, 1460-byte payload.

## Constraints

- **Only modify examples folder The exception is `lwipopts.h` files (they are per-example and safe to edit).

## Goals

Determine what the current CPU utilisation is measuring because we haven't specifically implemented CPU utilisation

Implement a benchmark for iperf3 on cpu utilisation similar to ipbench which runs on the echo server example. (the echo server something is bugging at the moment so running it probably wont work you can try fix it)

## ipbench benchmark testing method
  ipbench has two implementations -
   both avoid /proc/stat entirely,
  instead measuring CPU cycles
  directly.

  ---
  Method 1: cpu_target_lukem 
  (Modern - TSC-based)
  
  File: ipbench2/src/tests/cpu_targ
  et_lukem/cpu_target_lukem.c

  Core idea: A tight loop in a
  dedicated thread spins, reading
  the CPU's hardware timestamp
  counter (TSC) on every iteration.
   If the gap between two
  consecutive reads is small (below
   PROFILE_CONTEXT_COST cycles),
  the CPU was idle between them;
  otherwise it was doing real work.

  // Idle thread runs during the 
  entire test
  void *idle_thread(void *arg) {
      cycle_t x0, x1, delta, total,
   idle;
      idle = total = 0;
      x0 = get_cycles();
  // read TSC

      while (calc) {
          x1 = x0;
          x0 = get_cycles();
  // read TSC again
          delta = x0 - x1;
  // cycles elapsed
          total += delta;

          if (delta <
  PROFILE_CONTEXT_COST)  // 
  threshold = 300 cycles (default)
              idle += delta;
  // short gap → idle, classify as 
  idle time

          timer_buffer.idle  =
  idle;
          timer_buffer.total =
  total;
      }
  }

  // At test end:
  // CPU% = (1 - idle_cycles / 
  total_cycles) * 100
  cpu_util = (1.f - ((double)idle /
   (double)total)) * 100;

  TSC is read via inline assembly 
  per-arch (cpu_target_lukem.h):

  Arch: x86-64 / i386
  Instruction: rdtsc
  ─────────────────────────────────
  ─ 
  Arch: ARM64
  Instruction: mrs %0, cntvct_el0
  ─────────────────────────────────
  ─
  Arch: IA-64
  Instruction: ia64_get_itc()
  ─────────────────────────────────
  ─
  Arch: Alpha
  Instruction: rpcc

  Key parameter:
  PROFILE_CONTEXT_COST = 300
  cycles. This threshold separates
  a true idle gap from a
  context-switch preemption. If the
   loop was preempted, the gap will
   be large (>300 cycles) and
  counts as busy. If the CPU was
  genuinely idle and came back
  quickly, gap is small and counts
  as idle.

  ---
  Method 2: cpu_target (Legacy — 
  calibrated busy-loop)

  File: ipbench2/src/tests/cpu_targ
  et/cpu_target.c

  Core idea: Fork one process per
  CPU core. Each runs a calibrated
  busy-loop. A 1-second ITIMER_REAL
   signal samples how many loop
  iterations completed. The ratio
  vs. the unloaded calibration rate
   gives CPU utilisation.

  // Every second:
  for (i = 0; i < nr_cpus; i++) {
      current_rate =
  current_loop_count[i];  // 
  iterations in last second
      cpu_util[i] = 1.0 -
  (current_rate /
  calibrated_rate[i]);
      // if current_rate == 
  calibrated_rate → 0% util 
  (nothing displaced the loop)
      // if current_rate == 0      
          → 100% util (loop had no 
  time to run)
  }

  Requires a one-time calibration
  (-C flag) on an idle system that
  writes counts_per_sec to disk.

  ---
  Replicating in an iperf3 Client

  Use Method 1 (TSC approach) — it
  needs no calibration and works
  well during a bounded network
  test.

  Skeleton:

  #include <stdint.h>
  #include <pthread.h>
  #include <stdio.h>
  #include <time.h>

  // --- TSC reader (x86-64) ---
  static inline uint64_t 
  get_cycles(void) {
      uint32_t lo, hi;
      __asm__ volatile("rdtsc" : 
  "=a"(lo), "=d"(hi));
      return ((uint64_t)hi << 32) |
   lo;
  }

  // On ARM64, replace with:
  // static inline uint64_t
  get_cycles(void) {
  //     uint64_t v;
  //     __asm__ volatile("mrs %0, 
  cntvct_el0" : "=r"(v));
  //     return v;
  // }

  #define PROFILE_CONTEXT_COST 300
    // tune per machine; start at 
  300

  static volatile int measuring =
  0;
  static uint64_t g_idle = 0,
  g_total = 0;

  void *cpu_idle_thread(void *arg)
  {
      uint64_t x0, x1, delta;
      uint64_t idle = 0, total = 0;
      x0 = get_cycles();

      while (measuring) {
          x1 = x0;
          x0 = get_cycles();
          delta = x0 - x1;
          total += delta;
          if (delta <
  PROFILE_CONTEXT_COST)
              idle += delta;
      }
      g_idle  = idle;
      g_total = total;
      return NULL;
  }

  // --- Wrap your iperf3 test ---
  void run_iperf3_with_cpu(void) {
      pthread_t tid;
      measuring = 1;
      pthread_create(&tid, NULL,
  cpu_idle_thread, NULL);

      // --- run iperf3 here 
  (system(), exec, or libiperf 
  calls) ---

      measuring = 0;
      pthread_join(tid, NULL);

      double cpu_util = (1.0 -
  (double)g_idle / (double)g_total)
   * 100.0;
      printf("CPU utilisation: 
  %.1f%%\n", cpu_util);
  }

  Important notes for correct 
  results:
  1. Pin the idle thread to the 
  NIC's interrupt CPU if you want
  to measure the cost of packet
  processing specifically (use
  pthread_setaffinity_np).
  2. PROFILE_CONTEXT_COST needs
  tuning per machine — the ipbench
  calibrate binary (ipbench2/src/te
  sts/cpu_target_lukem/calibrate.c)
   does this by measuring minimum
  TSC delta between two reads on an
   idle system.
  3. The measurement thread must
  run at the same or higher 
  priority than the iperf3 workload
   or the idle ratio will be
  skewed. 
  4. This measures whole-CPU 
  utilization, not just network
  stack cost. To isolate
  NIC/softirq cost, compare
  measurements with and without
  traffic, or read /proc/softirqs
  deltas separately.



## iperf3 Testing Notes

Use `iperf3` for validating UDP/TCP networking functionality and benchmarking the custom network stack. Typical client usage is `iperf3 -c <server_ip> -u` for UDP mode, with common parameters including `-p` for port, `-t` for duration, `-b` for bandwidth target, `-l` for payload size, `-P` for parallel streams, and `-J` for JSON output. In QEMU user networking setups, the host is usually reachable at `10.0.2.2` and the guest often receives `10.0.2.15`. Example: `iperf3 -c 10.0.2.2 -u -t 5 -b 10M -l 1460`. Note that iperf3 is not just raw UDP traffic — it also requires a TCP control connection for parameter negotiation and statistics exchange. A custom implementation must therefore support both the TCP control protocol and UDP data path to be compatible with the official iperf3 client/server.

