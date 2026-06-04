# iperf3 Client — Usage

The active example is **`examples/iperf3_client/`**. It implements an iperf3
*client* that runs as an sDDF/Microkit application and talks to a standard
`iperf3 -s` server. It supports **TCP or UDP** selected at compile time
(`PROTOCOL=tcp|udp`). (`iperf3_udp/` is the older UDP-only version, kept only for
comparison.)

> **Hardware numbers are what matter.** QEMU validates correctness only — its
> throughput is capped by the single-threaded slirp NIC and its CPU-util / PMU /
> cycle counters are not representative of silicon. Run real benchmarks on a
> board (odroidc4 etc.) via the machine queue described below.

---

## How the test works

An iperf3 session is **not** just raw data packets — it has a TCP *control*
connection plus a *data* path:

1. **DHCP.** On boot the client brings up the lwIP netif and waits for a DHCP
   lease (prints `DHCP request finished, IP address ... is: 172.16.2.x`).
2. **Control connection (TCP, always).** The client connects to the server's
   control port (5202 for client0) and runs the iperf3 state machine:
   exchange cookie → `PARAM_EXCHANGE` (send the JSON test parameters) →
   `CREATE_STREAMS` → `TEST_START` → `TEST_RUNNING`. You can watch this on the
   serial as `[iperf3] server state byte = N`.
3. **Data path.**
   - **TCP**: the client opens `NUM_STREAMS` data connections and sends as fast
     as the send window allows. Send is ACK-clocked.
   - **UDP**: the client pumps datagrams at `TARGET_BW_MBPS` and the server
     reports throughput / loss / jitter.
4. **End of test.** The measured window excludes a warm-up/omit period, so the
   reported throughput is steady-state. At `omit_end` the benchmark PD resets its
   cycle/PMU counters; at test end the client prints its metrics and then
   `MQ_EXIT`.

---

## Metrics — what we measure and how it differs from iperf3

The board and the server measure **different things**. iperf3-the-protocol only
natively reports throughput / loss / jitter, all computed by the **server** from
the packets it receives. Everything about CPU cost and kernel behaviour is *our*
instrumentation added to the client — stock iperf3 has no equivalent. Because
the client *is* the lwIP stack, we can read counters iperf3 never sees.

The client prints these on the board serial (grep them from the mq.sh stdout /
`-l` logfile):

```
[cpu_util] 27.4% over 1 core(s) (busy=… idle=… total=… cycles)   ← util summed across cores
[pkts]     client=0 tx_segs=584109                                ← exact TCP segment count
[rtt]      min=2498 mean=3053 max=44720 sd=879 us (n=3246)        ← self-measured RTT (us)
MQ_EXIT                                                            ← machine-queue done signal
```

### `[cpu_util]` — CPU utilisation (`iperf3_client.c`)

Each core's benchmark/idle PD keeps two free-running cycle counters in shared
memory: `core_ccount` (total cycles) and `idle_ccount` (cycles spent in the
idle thread). At `omit_end` the client snapshots both per core and notifies
`start_ch` (which also resets the PMU); at TEST_END it reads them again, sums
the deltas across all cores, and reports `(total − idle) / total`.

- **vs iperf3:** iperf3 does not measure CPU at all. This is conceptually the
  **ipbench** idea, but inverted: ipbench *infers* idle by spinning a thread and
  watching for small TSC gaps (sampling, with a `PROFILE_CONTEXT_COST` threshold
  and one-off calibration). We instead read the **exact** idle-cycle count
  straight from the seL4 idle thread — no sampling, no threshold, no
  calibration. More accurate in principle, but only on real silicon: QEMU (TCG)
  doesn't model cycles, so the percentage there is junk.
- Requires `MICROKIT_CONFIG=benchmark`/`smp-benchmark`; otherwise it prints
  `no data`.

### `[pkts] tx_segs` — exact TCP segment count (`iperf3_client.c`)

Snapshots lwIP's `lwip_stats.tcp.xmit` (segments emitted by `tcp_output`) at
`omit_end` and again at TEST_END; the delta is the exact number of TCP segments
sent over the measured window.

- **vs iperf3:** iperf3's UDP path reports a datagram count, but for TCP it only
  knows *bytes* — segmentation happens in the kernel, invisible to it. We can
  read the segment count because lwIP is our own stack. This is what makes
  per-packet cost meaningful: `cycles ÷ tx_segs`, `kernel_entries ÷ tx_segs`, etc.

### `[rtt]` — self-measured round-trip time (`iperf3_stream_tcp.c`, aggregated in `iperf3_ctrl.c`)

Measured at the application layer. When no sample is in flight (and we're past
omit), the client records the current send byte-offset (`rtt_target`) and a
timestamp (`rtt_t0_ns`). On the ACK path it accumulates `rtt_acked`; once that
reaches the timed offset it computes `now − t0`. Keeping a single sample
outstanding gives ≈ one measurement per round-trip. It tracks
min/max/sum/sumsq/count and reports min/mean/max/stddev (integer sqrt — no libm).

- **vs iperf3:** iperf3 reports RTT only on Linux, by reading the kernel's
  smoothed estimate from `TCP_INFO.tcpi_rtt`. We have no `TCP_INFO`, so we time
  send→ACK latency ourselves at the byte-offset level. Different definition (raw
  ACK latency vs. kernel SRTT), so expect ours to read somewhat higher and
  noisier than Linux iperf3's.
- UDP has no ACKs, so there is no RTT — **jitter** (server-side) is its latency
  proxy instead.

### Throughput / loss / jitter — from the server JSON

These come from the **server's** report (`end.sum_received` in the JSON on
vb01), computed exactly as for any real iperf3 client — that's the payoff of
being protocol-compatible. The TCP client also stuffs its self-measured cpu_util
and RTT into the `EXCHANGE_RESULTS` JSON, so they appear in the server's report
too.

### PMU / kernel counters — from the benchmark PDs

When built with `benchmark`/`smp-benchmark`, the per-core benchmark PDs also
print kernel cycles, kernel entries, schedules, total cycles, and PMU counters
(L1 i/d cache + i/d tlb misses, instructions, branch mispredicts), both
system-total-per-core and per-PD. User cycles = Total − Kernel. **On QEMU the
cycle/PMU values are junk; the counts (tx_segs, entries, schedules) and RTT are
the QEMU-meaningful ones. On hardware they're all real.**

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
| `TARGET_BW_MBPS` | N | UDP rate target (and TCP pacing) |
| `NUM_STREAMS` | N | TCP parallel streams (default 1) |

Built image: **`build/loader.img`**.

### Core configs (and how many servers each needs)

| config | layout | MICROKIT_CONFIG | clients | servers |
|---|---|---|---|---|
| `single_core` | everything on core 0 | `benchmark` | 1 | 5202 |
| `two_core` | client0+timer c0; eth+virt_tx c1 | `smp-benchmark` | 1 | 5202 |
| `four_core` | virt_rx+timer c0; eth+virt_tx c1; client0+copier c2; client1+copier c3 | `smp-benchmark` | 2 | 5202 **and** 5203 |

**N clients need N servers** — client *i* targets port `5202+i`. Verify which
config actually built (the SDF is ground truth):

```sh
grep -oE 'name="(client|bench)[0-9]+"' build/iperf3.system | sort -u
# client0 + bench0 only  → single_core
# client0 client1 bench0..3 → four_core
```

### Rebuild rules (flag changes don't always recompile)

- Changing **PROTOCOL** or **SMP_CONFIG**: `make clean` first (stale SDF/objects).
- Changing only **TARGET_BW_MBPS** / **NUM_STREAMS** (same protocol+config):
  `touch iperf3_ctrl.c && make ...` recompiles just that file (fast — fine for a sweep).
- First build for a new board: `make clean`.
- If lwipopts.h edits seem to have no effect: `make clobber` (a stale suffixed
  `lib_sddf_lwip_iperf_client.a` survives plain `make clean`).

---

## Running on SSH boards (the machine queue)

### Network topology

- **`ssh tftp.keg.cse.unsw.edu.au`** ("tftp") — hosts images and the machine queue (`~/machine_queue`).
- **`ssh vb01`** — the iperf3 **server** host. Use no extra SSH flags.
- Boards DHCP from `172.16.0.0/16` (odroidc4 gets `172.16.2.x`).
- vb01 has two interfaces; boards can only reach **`172.16.0.101`** — use that as
  `SERVER_IP`. (The `10.13.1.5` interface is unreachable from boards.)

The flow for each run is **build → scp image to tftp → `mq.sh run` against the
board**. The machine queue boots `loader.img` on the board and watches the serial
for the `-c 'MQ_EXIT'` string to know the test finished.

### 1. Start the iperf3 server(s) on vb01

Use **tmux**, not `nohup … &`. The reason: `nohup` only ignores **SIGHUP**, but
when your `ssh vb01 "… &"` command returns, systemd-logind tears down the login
session's cgroup scope and sends **SIGTERM** to everything in it — which `nohup`
does *not* catch. So a backgrounded server dies a moment after the ssh call
returns (silently — the ssh call looks successful), before the board ever
connects. tmux's server **double-forks into its own daemon scope** that isn't
tied to the ssh session, so it survives:

```sh
ssh vb01 "tmux kill-session -t iperf5202 2>/dev/null; tmux new-session -d -s iperf5202 'iperf3 -s -p 5202 --json --forceflush > /tmp/iperf3_server.log 2>&1'"
# four_core needs a second server on 5203:
ssh vb01 "tmux kill-session -t iperf5203 2>/dev/null; tmux new-session -d -s iperf5203 'iperf3 -s -p 5203 --json --forceflush > /tmp/iperf3_server_5203.log 2>&1'"
# verify from a FRESH ssh that it survived:
ssh vb01 "ss -tlnp 2>/dev/null | grep :5202 && echo LISTENING || echo 'not listening'"
```

The server log is **cumulative** (one JSON object per test, appended). Restart
the server (kill + new tmux) at the start of each sweep so results map 1:1 to
runs. Kill the servers when done:

```sh
ssh vb01 "tmux kill-session -t iperf5202 2>/dev/null; tmux kill-session -t iperf5203 2>/dev/null; true"
```

### 2. Build, copy, and run one test

```sh
cd examples/iperf3_client

# single-core UDP at 500 Mbps
make MICROKIT_BOARD=odroidc4 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0 \
     MICROKIT_CONFIG=benchmark PROTOCOL=udp SMP_CONFIG=core_config/single_core.json \
     TARGET_BW_MBPS=500 SERVER_IP=172.16.0.101

scp build/loader.img lukez@tftp.keg.cse.unsw.edu.au:~/loader.img

ssh tftp.keg.cse.unsw.edu.au \
  "cd ~/machine_queue && ./mq.sh run -s odroidc4_1 -f ~/loader.img -c 'MQ_EXIT' -d 120 -l /tmp/bench.log" \
  2>&1 | grep -E "DHCP|cpu_util|\[rtt\]|\[pkts\]|MQ_EXIT|Timeout|Shutting"
```

`mq.sh run` flags: `-s` board name (`odroidc4_1`), `-f` image, `-c` the
done-string to wait for, `-d` timeout in seconds, `-l` optional logfile.

### 3. Sweep a parameter

```sh
for BW in 100 200 300 400 500 600 700 800 900 1000; do
  touch iperf3_ctrl.c   # forces TARGET_BW_MBPS recompile without a full clean
  make MICROKIT_BOARD=odroidc4 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0 \
       MICROKIT_CONFIG=benchmark PROTOCOL=udp SMP_CONFIG=core_config/single_core.json \
       TARGET_BW_MBPS=${BW} SERVER_IP=172.16.0.101
  scp build/loader.img lukez@tftp.keg.cse.unsw.edu.au:~/loader.img
  ssh tftp.keg.cse.unsw.edu.au \
    "cd ~/machine_queue && ./mq.sh run -s odroidc4_1 -f ~/loader.img -c 'MQ_EXIT' -d 120 -l /tmp/bench_${BW}mbps.log" \
    2>&1 | grep -E "DHCP|cpu_util|\[rtt\]|\[pkts\]|MQ_EXIT|Timeout|Shutting"
done
```

For a four-core TCP run instead: `make clean` first, then
`MICROKIT_CONFIG=smp-benchmark PROTOCOL=tcp SMP_CONFIG=core_config/four_core.json`
(and make sure both servers, 5202 and 5203, are up).

### 4. Fetch server-side stats (UDP)

The board serial gives cpu_util / RTT / packet counts; the server JSON gives
throughput, loss, and jitter:

```sh
ssh vb01 "cat /tmp/iperf3_server.log" | python3 -c "
import sys, json
text = sys.stdin.read(); objects=[]; depth=0; start=None
for i,c in enumerate(text):
    if c=='{':
        if depth==0: start=i
        depth+=1
    elif c=='}':
        depth-=1
        if depth==0 and start is not None: objects.append(text[start:i+1]); start=None
for idx,obj in enumerate(objects):
    d=json.loads(obj); sr=d['end']['sum_received']
    print(f'Test {idx+1}: {sr[\"bits_per_second\"]/1e6:.1f} Mbps  loss={sr[\"lost_percent\"]:.2f}%  jitter={sr[\"jitter_ms\"]:.4f}ms  pkts={sr[\"packets\"]}  lost={sr[\"lost_packets\"]}')
"
```

For TCP, throughput is `end.sum_received.bits_per_second` (no loss/jitter);
RTT/packets come from the board's `[rtt]` / `[pkts]` serial lines.

---

## Running on QEMU (correctness check)

The `run.sh` helper bakes in the right flags (QEMU-only — it runs `make qemu`):

```sh
cd examples/iperf3_client
./run.sh single udp      # 1 client, 1 core, UDP   (start: iperf3 -s -p 5202)
./run.sh four   tcp      # 2 clients, 4 cores, TCP  (start: 5202 AND 5203)
./run.sh two    tcp 5    # 1 client, 2 cores, TCP, 5 parallel streams
```

It prints which `iperf3 -s -pNNNN` servers to start first, then does
`make clean` + `make qemu` with the matching `MICROKIT_CONFIG` and `SMP_CONFIG`.
QEMU's server is reachable at `10.0.2.2`.

Raw equivalent (one line — backslash continuations silently drop flags when pasted):

```sh
make clean MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0
make qemu MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0 PROTOCOL=tcp NUM_STREAMS=1 MICROKIT_CONFIG=smp-benchmark SMP_CONFIG=core_config/four_core.json
```

> **QEMU caveats:** aggregate TCP caps at ~900 Mbps (slirp ceiling); a single
> stream ≈ 160 Mbps (real lwIP window limit). `four_core` UDP sends 0 bytes
> under QEMU because the cross-core `net_tx` "buffers free" notification is never
> delivered — that path only works on `single_core`/`two_core` in QEMU and is
> exactly what hardware should validate.

---

## TCP send window (single-stream bottleneck)

A single lwIP TCP stream is window-limited: throughput ≈ `TCP_SND_BUF / RTT`, so
`TCP_SND_BUF` must be ≥ the bandwidth-delay product of the path (`link_rate ×
RTT`). The current default is `TCP_SND_BUF = 256 KB` in
`examples/iperf3_client/include/lwip/lwipopts.h` (~640 Mbps single stream in
QEMU vs ~200 Mbps at the old 30000). Re-measure the knee on hardware. The
receive window (`TCP_WND`) is pinned ≤ 65535 because `TCP_RCV_SCALE=0`.
