# iperf3 Client - Usage

## How the test works

1. **DHCP.** On boot the client brings up the lwIP netif and waits for a DHCP
   lease (prints `DHCP request finished, IP address ... is: 172.16.2.x`).
2. **Control connection (TCP).** The client connects to the server's
   control port (5202 for client0) and runs the iperf3 state machine:
   exchange cookie → `PARAM_EXCHANGE` (send the JSON test parameters) →
   `CREATE_STREAMS` → `TEST_START` → `TEST_RUNNING`. You can watch this on the
   serial as `[iperf3] server state byte = N`.
3. **Data path.**
   - **TCP**: the client opens `NUM_STREAMS` data connections and sends as fast
     as the send window allows at `TARGET_BW_MBPS`. Send is ACK-clocked.
   - **UDP**: the client pumps datagrams at `TARGET_BW_MBPS` and the server
     reports throughput / loss / jitter.
4. **End of test.** The measured window excludes a warm-up/omit period, so the
   reported throughput is steady-state. At `omit_end` the benchmark PD resets its
   cycle/PMU counters; at test end the client prints its metrics and then
   `MQ_EXIT`.

---

## Metrics - what we measure and how it differs from iperf3

The board and the server measure **different things**. iperf3-the-protocol only
natively reports throughput / loss / jitter, all computed by the **server** from
the packets it receives. Everything about CPU cost and kernel behaviour is *our*
instrumentation added to the client  stock iperf3 has no equivalent. Because
the client *is* the lwIP stack, we can read counters iperf3 never sees.

The client prints these on the board serial (can grep them from the mq.sh stdout /
`-l` logfile):

```
[cpu_util] 27.4% over 1 core(s) (busy=… idle=… total=… cycles)   ← util summed across cores
[pkts]     client=0 tx_segs=584109                                ← exact TCP segment count
[rtt]      min=2498 mean=3053 max=44720 sd=879 us (n=3246)        ← self-measured RTT (us)
MQ_EXIT                                                            ← machine-queue done signal
```

### `[cpu_util]` - CPU utilisation (`iperf3_client.c`)

Each core's benchmark/idle PD keeps two free-running cycle counters in shared
memory: `core_ccount` (total cycles) and `idle_ccount` (cycles spent in the
idle thread). At `omit_end` the client snapshots both per core and notifies
`start_ch` (which also resets the PMU); at TEST_END it reads them again, sums
the deltas across all cores, and reports `(total − idle) / total`.

- **vs iperf3:** iperf3 does not measure CPU at all. This is conceptually the
  **ipbench** idea, but inverted: ipbench *infers* idle by spinning a thread and
  watching for small TSC gaps (sampling, with a `PROFILE_CONTEXT_COST` threshold
  and one-off calibration). We instead read the **exact** idle-cycle count
  straight from the seL4 idle thread - no sampling, no threshold, no
  calibration. More accurate in principle, but only on real silicon: QEMU (TCG)
  doesn't model cycles, so the percentage there is junk.
- Requires `MICROKIT_CONFIG=benchmark`/`smp-benchmark`; otherwise it prints
  `no data`.

### `[pkts] tx_segs` - exact TCP segment count (`iperf3_client.c`)

Snapshots lwIP's `lwip_stats.tcp.xmit` (segments emitted by `tcp_output`) at
`omit_end` and again at TEST_END; the delta is the exact number of TCP segments
sent over the measured window.

- **vs iperf3:** iperf3's UDP path reports a datagram count, but for TCP it only
  knows *bytes* - segmentation happens in the kernel, invisible to it. We can
  read the segment count because lwIP is our own stack. This is what makes
  per-packet cost meaningful: `cycles ÷ tx_segs`, `kernel_entries ÷ tx_segs`, etc.

### `[rtt]` - self-measured round-trip time (`iperf3_stream_tcp.c`, aggregated in `iperf3_ctrl.c`)

Measured at the application layer. When no sample is in flight (and we're past
omit), the client records the current send byte-offset (`rtt_target`) and a
timestamp (`rtt_t0_ns`). On the ACK path it accumulates `rtt_acked`; once that
reaches the timed offset it computes `now − t0`. Keeping a single sample
outstanding gives ≈ one measurement per round-trip. It tracks
min/max/sum/sumsq/count and reports min/mean/max/stddev (integer sqrt - no libm).

- **vs iperf3:** iperf3 reports RTT only on Linux, by reading the kernel's
  smoothed estimate from `TCP_INFO.tcpi_rtt`. We have no `TCP_INFO`, so we time
  send→ACK latency ourselves at the byte-offset level. Different definition (raw
  ACK latency vs. kernel SRTT), so expect ours to read somewhat higher and
  noisier than Linux iperf3's.
- UDP has no ACKs, so there is no RTT - **jitter** (server-side) is its latency
  proxy instead.

### Throughput / loss / jitter - from the server JSON

These come from the **server's** report (`end.sum_received` in the JSON on
vb01), computed exactly as for any real iperf3 client - that's the payoff of
being protocol-compatible. The TCP client also stuffs its self-measured cpu_util
and RTT into the `EXCHANGE_RESULTS` JSON, so they appear in the server's report
too.

### PMU / kernel counters - from the benchmark PDs

When built with `benchmark`/`smp-benchmark`, the per-core benchmark PDs also
print kernel cycles, kernel entries, schedules, total cycles, and PMU counters
(L1 i/d cache + i/d tlb misses, instructions, branch mispredicts), both
system-total-per-core and per-PD. User cycles = Total − Kernel.

---

## Build flags (`examples/iperf3_client/`)

| flag | values | notes |
|---|---|---|
| `MICROKIT_BOARD` | e.g. `odroidc4`, `qemu_virt_aarch64` | **required** |
| `MICROKIT_SDK` | path | **required** |
| `PROTOCOL` | `tcp` \| `udp` | default `udp` |
| `MICROKIT_CONFIG` | `benchmark` (single_core) \| `smp-benchmark` (two/four core) | needed for cpu_util/PMU data |
| `SMP_CONFIG` | `core_config/{single,two,four}_core.json` | core layout (default `single_core`) |
| `SERVER_IP` | a.b.c.d | **mandatory for hardware** (`172.16.0.101`); QEMU default `10.0.2.2` |
| `TARGET_BW_MBPS` | N | rate target for **both** UDP and TCP; **per stream**, so aggregate ≈ N×`NUM_STREAMS`. Caps only (won't exceed window). Unset = unlimited |
| `NUM_STREAMS` | N | TCP parallel streams (default 1) |

Built image: **`build/loader.img`**.

### Core configs (and how many servers each needs)

| config | layout | MICROKIT_CONFIG | clients | servers |
|---|---|---|---|---|
| `single_core` | everything on core 0 | `benchmark` | 1 | 5202 |
| `two_core` | client0+timer c0; eth+virt_tx c1 | `smp-benchmark` | 1 | 5202 |
| `four_core` | virt_rx+timer c0; eth+virt_tx c1; client0+copier c2; client1+copier c3 | `smp-benchmark` | 2 | 5202 **and** 5203 |

**N clients need N servers** - client *i* targets port `5202+i`. 
```

### Rebuild rules (flag changes don't always recompile)

- Changing **PROTOCOL** or **SMP_CONFIG**: `make clean` first (stale SDF/objects).
- Changing only **TARGET_BW_MBPS** / **NUM_STREAMS** (same protocol+config):
  `touch iperf3_ctrl.c && make ...` recompiles just that file (fast - fine for a sweep).
- First build for a new board: `make clean`.
- If lwipopts.h edits seem to have no effect: `make clobber` (a stale suffixed
  `lib_sddf_lwip_iperf_client.a` survives plain `make clean`).

---

## Running on SSH boards (the machine queue)

### Build, copy, and run one test

```sh
cd examples/iperf3_client

# single-core UDP at 500 Mbps
make MICROKIT_BOARD=odroidc4 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0 \
     MICROKIT_CONFIG=benchmark PROTOCOL=udp SMP_CONFIG=core_config/single_core.json \
     TARGET_BW_MBPS=500 SERVER_IP=172.16.0.101

scp build/loader.img lukez@tftp.keg.cse.unsw.edu.au:~/test.img

ssh tftp.keg.cse.unsw.edu.au \
  "cd ~/machine_queue && ./mq.sh run -s odroidc4_1 -f ~/test.img -c 'MQ_EXIT' -d 120
```

For a four-core TCP run instead: `make clean` first, then
`MICROKIT_CONFIG=smp-benchmark PROTOCOL=tcp SMP_CONFIG=core_config/four_core.json`
(and make sure both servers, 5202 and 5203, are up).

For additional metrics you can log the serial output


For TCP, throughput is `end.sum_received.bits_per_second` (no loss/jitter);
RTT/packets come from the board's `[rtt]` / `[pkts]` serial lines.

---

## Example
```sh
make clean MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0
make qemu MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0 PROTOCOL=tcp NUM_STREAMS=1 MICROKIT_CONFIG=smp-benchmark SMP_CONFIG=core_config/four_core.json
```

## TCP send window (single-stream bottleneck)

A single lwIP TCP stream is window-limited: throughput ≈ `TCP_SND_BUF / RTT`, so
`TCP_SND_BUF` must be ≥ the bandwidth-delay product of the path (`link_rate ×
RTT`). The current default is `TCP_SND_BUF = 256 KB` in
`examples/iperf3_client/include/lwip/lwipopts.h` (~640 Mbps single stream in
QEMU vs ~200 Mbps at the old 30000). Re-measure the knee on hardware. The
receive window (`TCP_WND`) is pinned ≤ 65535 because `TCP_RCV_SCALE=0`.
