# iperf3 Client - Usage

## Runtime control (serial `start` command)

The client is driven **at runtime over the serial console** — server IP,
duration, streams, bandwidth and payload are typed in, not baked in at compile
time. One boot can run many tests.

After DHCP the client prints a prompt and waits:

```
DHCP request finished, IP address for netif client0 is: 172.16.4.4
Ready. Type 'start <server_ip> [opts]' to run an iperf3 TCP test (or 'help').
iperf3>
```

Commands:

```
start [tcp|udp] <ip> [port] [dur_s] [streams] [bw_mbps] [len]
status
help
```

| `start` arg | default | meaning |
|---|---|---|
| `tcp\|udp` | build `PROTOCOL=` | **protocol for this test** (both are in the image) |
| `ip` | — | server IPv4 (**required**) |
| `port` | 5202 | iperf3 server port |
| `dur_s` | 10 (TCP) / 5 (UDP) | test duration, seconds |
| `streams` | 1 | parallel streams (1–15) |
| `bw_mbps` | 0 | rate target; 0 = unlimited |
| `len` | 1460 | UDP datagram bytes (**ignored for TCP** — it writes 16 KB chunks) |

Example: `start tcp 172.16.0.101 5202 10 4 1000` (TCP, 10 s, 4 streams, 1 Gbit target).
**Protocol is now runtime too** — both TCP and UDP are compiled into every image, so
the same binary can run `start tcp ...` and then `start udp ...`. `PROTOCOL=` only
sets the default used when the token is omitted. After a test finishes you return to
`iperf3>` for the next run.

**Multi-client (four_core):** only client0 receives serial input, so it acts as
*controller* — it writes the typed params to a shared memory region and notifies
the other client(s), which run the **same** test concurrently against
`base_port + client_id` (client0→5202, client1→5203). This relies on cross-core
notifications, which work on hardware (validated on odroidc4) but **not** under
QEMU SMP.

## How the test works

1. **DHCP, then wait for `start`.** On boot the client brings up the lwIP netif,
   waits for a DHCP lease (`DHCP request finished, IP address ... is: 172.16.x.x`),
   then prints `iperf3>` and waits for a `start` command (above).
2. **Control connection (TCP).** On `start`, the client connects to the server's
   control port and runs the iperf3 state machine:
   exchange cookie → `PARAM_EXCHANGE` (send the JSON test parameters) →
   `CREATE_STREAMS` → `TEST_START` → `TEST_RUNNING`. You can watch this on the
   serial as `[iperf3] server state byte = N`.
3. **Data path.**
   - **TCP**: the client opens `streams` data connections and sends as fast
     as the send window allows, capped at `bw_mbps`. Send is ACK-clocked.
   - **UDP**: the client pumps datagrams at `bw_mbps` and the server
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
| `PROTOCOL` | `tcp` \| `udp` | **default** protocol only (both compiled in); runtime `start [tcp\|udp]` overrides |
| `MICROKIT_CONFIG` | `benchmark` (single_core) \| `smp-benchmark` (two/four core) | needed for cpu_util/PMU data |
| `SMP_CONFIG` | `core_config/{single,two,four}_core.json` | core layout (default `single_core`) |

Server IP, port, duration, **streams** and **bandwidth** are no longer build
flags — they are runtime arguments to the serial `start` command (see top).
`SERVER_IP` is still accepted (it's injected into each client's `app_config`) but
the client ignores it; the address comes from `start`. The old `NUM_STREAMS` /
`TARGET_BW_MBPS` `-D` flags have been removed.

Built image: **`build/loader.img`**.

### Core configs (and how many servers each needs)

| config | layout | MICROKIT_CONFIG | clients | servers |
|---|---|---|---|---|
| `single_core` | everything on core 0 | `benchmark` | 1 | 5202 |
| `two_core` | client0+timer c0; eth+virt_tx c1 | `smp-benchmark` | 1 | 5202 |
| `four_core` | virt_rx+timer c0; eth+virt_tx c1; client0+copier c2; client1+copier c3 | `smp-benchmark` | 2 | 5202 **and** 5203 |

**N clients need N servers** - client *i* targets port `5202+i`.

### Rebuild rules (flag changes don't always recompile)

- Changing **PROTOCOL** or **SMP_CONFIG**: `make clean` first (stale SDF/objects).
- Stream count / bandwidth no longer need a rebuild — they're runtime `start` args.
- First build for a new board: `make clean`.
- If lwipopts.h edits seem to have no effect: `make clobber` (a stale suffixed
  `lib_sddf_lwip_iperf_client.a` survives plain `make clean`).

---

## Running a test on the hardware (the machine queue)

### The three machines (who's who)

| machine | role | how you reach it |
|---|---|---|
| **vb01** | runs the `iperf3 -s` server(s); the board reaches it at **172.16.0.101** | `ssh vb01` |
| **tftp.keg.cse.unsw.edu.au** | the machine-queue host — `mq.sh` runs *here*, the board netboots its image from *here*, and this is where you upload `loader.img` | `ssh lukez@tftp.keg.cse.unsw.edu.au` |
| **odroidc4_1** | the board under test — `mq.sh` power-cycles it, netboots the image, and bridges its serial console back to you | (via `mq.sh`, not directly) |

Key point: the client waits for a typed `start`, so the old headless
`mq.sh run ... -c 'MQ_EXIT'` (read-only console) can't drive it. You boot with
`mq.sh run -a` (keep-alive), which **forwards your stdin to the board's UART**
once the `-c` regex matches — then you type/pipe the `start` command.

### Step 1 — start the server(s) on vb01

One `iperf3 -s -p P` serves both TCP and UDP tests on that port. N clients need N
servers on consecutive ports (`5202`, `5203`, …).

```sh
ssh vb01 'setsid sh -c "iperf3 -s -p 5202 --json --forceflush >/tmp/iperf3_5202.log 2>&1 </dev/null" &'
# four_core also needs :5203
ssh vb01 'ss -tlnp | grep :5202'    # confirm it is LISTENing
```

### Step 2 — build the image (on your machine)

```sh
cd examples/iperf3_client
make MICROKIT_BOARD=odroidc4 MICROKIT_SDK=/path/to/microkit-sdk-2.1.0 \
     MICROKIT_CONFIG=benchmark SMP_CONFIG=core_config/single_core.json
# -> build/loader.img   (no SERVER_IP / PROTOCOL needed — both are runtime now)
```

### Step 3 — upload the image to the tftp host

`mq.sh` netboots from the tftp host, so the image must live there. Put it in your
**home dir** — the tftp host wipes `/tmp`.

```sh
scp build/loader.img lukez@tftp.keg.cse.unsw.edu.au:luke_iperf.img
```

### Step 4 — boot and drive the console

**Interactive** (you watch and type). Match the completion regex on the flushed
`Ready` line — the `iperf3>` prompt is emitted per-char colour-wrapped and isn't a
greppable contiguous string:

```sh
ssh -tt lukez@tftp.keg.cse.unsw.edu.au \
  "cd ~/machine_queue && ./mq.sh run -s odroidc4_1 -f ~/luke_iperf.img -c 'run an iperf3' -a -d 250"
# wait for:  Ready. Type 'start [tcp|udp] <server_ip> [opts]' ...
# then type: start tcp 172.16.0.101 5202 10 1 0
```

**Scripted** (pipe the command in — it's forwarded the moment interact starts,
right after the `Ready` line — capture the console, stop on `MQ_EXIT`):

```sh
: > /tmp/hw.log
( until grep -aq 'run an iperf3' /tmp/hw.log; do sleep 2; done
  sleep 3; printf 'start tcp 172.16.0.101 5202 10 1 0\r'
  until grep -aq MQ_EXIT /tmp/hw.log; do sleep 2; done; sleep 3 ) \
| ssh -tt lukez@tftp.keg.cse.unsw.edu.au \
    "cd ~/machine_queue && ./mq.sh run -s odroidc4_1 -f ~/luke_iperf.img -c 'run an iperf3' -a -d 250" \
    >/tmp/hw.log 2>&1
```

To sweep, just send more `start` lines on the same boot (wait for each `MQ_EXIT`):
`start udp 172.16.0.101 5202 5 1 200`, `start tcp 172.16.0.101 5202 10 4 1000`, …

### Step 5 — read the results

- **board serial** (in `/tmp/hw.log`): `[cpu_util]`, `[rtt]`, `[pkts]`, `MQ_EXIT`.
- **server throughput**: `ssh vb01 cat /tmp/iperf3_5202.log` → parse
  `end.sum_received.bits_per_second` (UDP also has `jitter_ms` / `lost_percent`).

### four_core (two concurrent clients)

```sh
make clean MICROKIT_BOARD=odroidc4 MICROKIT_SDK=/path/...
make  MICROKIT_BOARD=odroidc4 MICROKIT_SDK=/path/... \
      MICROKIT_CONFIG=smp-benchmark SMP_CONFIG=core_config/four_core.json
```
Start servers on **5202 and 5203**, then type **one** `start` on client0 — client1
runs the same params against `base_port + 1` automatically.

### Gotchas (learned running these)

- **Free the board lock if a run is interrupted.** Killing the interactive run
  doesn't always release it; a later run then says *"lock held by lukez"*. Free it:
  `ssh lukez@tftp... "cd ~/machine_queue && ./mq.sh sem -signal odroidc4_1"`
  (check with `./mq.sh sem -info odroidc4_1`).
- **Match `run an iperf3`, not `iperf3>`** — the prompt isn't a contiguous string.
- **Upload to your home dir, not `/tmp`** — the tftp host cleans `/tmp` between runs.
- **Boot PHY timeouts auto-retry** (`N tries remaining…`) — harmless, just wait.
- The old `bench.sh` uses the read-only `-c 'MQ_EXIT'` flow and **won't drive** the
  runtime client; use the `-a` interactive flow above instead.

### Verified hardware result (odroidc4, single_core, TCP)

`start 172.16.0.101 5202 10 1 0` against `iperf3 -s` on vb01 (1 GbE):

```
[pkts] client=0 tx_segs=814631
[cpu_util] 80.6% over 1 core(s) (busy=9679697497 idle=2327650853 total=12007348350 cycles)
[rtt] min=101 mean=2221 max=2464 sd=129 us (n=4475)
```
server-side: **938 Mbps** received (single TCP stream ≈ line rate) at **80.6% of one core**.

### Verified runtime protocol switch (odroidc4, single_core, one image)

From a **single image**, `start tcp ...` then `start udp ...` on one boot:
```
start tcp 172.16.0.101 5202 5 1 0    -> server: 938.1 Mbps, [cpu_util] 81.9%
start udp 172.16.0.101 5202 5 1 200  -> server: 92.2 Mbps, jitter 0.011ms (UDP path: connect reply -> SEND_PAYLOAD)
```
Both protocols run from the same binary — `PROTOCOL=` is only the default.

### Verified multi-client (odroidc4, four_core, TCP)

One typed `start 172.16.0.101 5202 10 1 0` on client0 drove **both** clients:
```
[multi] broadcast test to 1 peer(s)
Starting iperf3 (TCP) -> 172.16.0.101:5203   (client1, via cross-core notify)
Starting iperf3 (TCP) -> 172.16.0.101:5202   (client0)
```
The controller→peer broadcast works cross-core on real hardware. **However**
four_core throughput is heavily degraded — ~11 Mbps per client, `[cpu_util] 1.0%
over 4 cores` (99% idle), `[rtt] mean=171ms`: both clients stall on the cross-core
data path (clients on cores 2/3 depend on `net_virt_tx`/eth on core 1). This is the
known multi-core data-path bottleneck, not a coordination bug. **single_core is the
config that saturates the link;** four_core is for studying the multi-core path.

---

## Example (QEMU)
```sh
make clean MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0
make qemu  MICROKIT_BOARD=qemu_virt_aarch64 MICROKIT_SDK=/Users/lululululluke/sddf/microkit-sdk-2.1.0 PROTOCOL=tcp MICROKIT_CONFIG=benchmark SMP_CONFIG=core_config/single_core.json
```
QEMU wires your terminal to the board's serial (`-nographic`), so when `iperf3>`
appears you can just type `start 10.0.2.2 5202 10 1 0` (run `iperf3 -s -p 5202` on
the host first). Notes: QEMU is the throughput ceiling (numbers aren't
representative — measure on hardware); cross-core notifications don't work under
QEMU SMP, so four_core multi-client and UDP only work on single/two_core there;
and some hosts hit a pre-existing virtio-net eth-driver fault at boot under QEMU.

## TCP send window (single-stream bottleneck)

A single lwIP TCP stream is window-limited: throughput ≈ `TCP_SND_BUF / RTT`, so
`TCP_SND_BUF` must be ≥ the bandwidth-delay product of the path (`link_rate ×
RTT`). The current default is `TCP_SND_BUF = 256 KB` in
`examples/iperf3_client/include/lwip/lwipopts.h` (~640 Mbps single stream in
QEMU vs ~200 Mbps at the old 30000). Re-measure the knee on hardware. The
receive window (`TCP_WND`) is pinned ≤ 65535 because `TCP_RCV_SCALE=0`.
