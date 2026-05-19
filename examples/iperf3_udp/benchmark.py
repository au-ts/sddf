#!/usr/bin/env python3
"""
iperf3_udp benchmark — sweeps requested bandwidth 100–1000 Mbps (1 stream, 1460B payload).
Builds with TARGET_BW_MBPS per level, runs iperf3 server + QEMU, collects results.

Usage:
    python3 benchmark.py [--sdk PATH] [--board BOARD] [--bandwidths 100,200,...]
"""

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time

EXAMPLE_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SDK  = os.path.join(EXAMPLE_DIR, "../../microkit-sdk-2.1.0")
DEFAULT_BOARD = "qemu_virt_aarch64"
PORT = 5202
BANDWIDTHS = [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]


def run_make(args, check=True):
    return subprocess.run(
        args, cwd=EXAMPLE_DIR,
        capture_output=True, text=True, check=check
    )


def kill_proc_group(proc):
    try:
        pgid = os.getpgid(proc.pid)
        os.killpg(pgid, signal.SIGTERM)
        proc.wait(timeout=3)
    except (ProcessLookupError, PermissionError, subprocess.TimeoutExpired):
        try:
            proc.kill()
        except Exception:
            pass


def collect_qemu_lines(proc):
    lines = []
    try:
        for line in proc.stdout:
            lines.append(line)
    except Exception:
        pass
    return lines


def parse_cpu_util(lines):
    for line in lines:
        m = re.search(r'\[cpu_util\]\s+([\d.]+)%', line)
        if m:
            return float(m.group(1))
    return None


def benchmark_one(bw_mbps, sdk, board):
    print(f"\n=== {bw_mbps} Mbps ===")

    # Touch ctrl source to force recompile with new bitrate/burst_max
    ctrl_src = os.path.join(EXAMPLE_DIR, "iperf3_ctrl.c")
    os.utime(ctrl_src)

    result = run_make(
        ["make", f"TARGET_BW_MBPS={bw_mbps}", "MICROKIT_CONFIG=benchmark",
         f"MICROKIT_BOARD={board}", f"MICROKIT_SDK={sdk}"],
        check=False
    )
    if result.returncode != 0:
        print(f"  Build failed:\n{result.stderr[-500:]}")
        return {"requested_mbps": bw_mbps, "error": "build_failed"}
    print("  Build OK")

    server = subprocess.Popen(
        ["iperf3", "-s", f"-p{PORT}", "--one-off", "--json", "--forceflush"],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    time.sleep(0.3)

    qemu = subprocess.Popen(
        ["make", "qemu", f"TARGET_BW_MBPS={bw_mbps}", "MICROKIT_CONFIG=benchmark",
         f"MICROKIT_BOARD={board}", f"MICROKIT_SDK={sdk}"],
        cwd=EXAMPLE_DIR,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        start_new_session=True
    )
    qemu_lines = []
    qemu_reader = threading.Thread(
        target=lambda: qemu_lines.extend(collect_qemu_lines(qemu)),
        daemon=True
    )
    qemu_reader.start()

    timeout_s = 40
    server_json = None
    try:
        stdout, _ = server.communicate(timeout=timeout_s)
        server_json = json.loads(stdout)
    except subprocess.TimeoutExpired:
        print("  TIMEOUT")
        server.kill()
    except json.JSONDecodeError as e:
        print(f"  JSON parse error: {e}")
    finally:
        kill_proc_group(qemu)
        qemu_reader.join(timeout=3.0)
        time.sleep(0.5)

    if server_json is None:
        return {"requested_mbps": bw_mbps, "error": "failed"}

    end = server_json.get("end", {})
    sr = end.get("sum_received") or end.get("sum", {})
    seconds = sr.get("seconds", 5)
    total_pkts = sr.get("packets", 0)
    cpu_util = parse_cpu_util(qemu_lines)

    result = {
        "requested_mbps": bw_mbps,
        "recv_mbps":      round(sr.get("bits_per_second", 0) / 1e6, 2),
        "lost_percent":   round(sr.get("lost_percent", 0), 2),
        "jitter_ms":      round(sr.get("jitter_ms", 0), 4),
        "lost_packets":   sr.get("lost_packets", 0),
        "total_packets":  total_pkts,
        "out_of_order":   sr.get("out_of_order", 0),
        "pps":            round(total_pkts / max(seconds, 0.001), 1),
        "seconds":        round(seconds, 2),
        "cpu_util_pct":   cpu_util,
    }
    cpu_str = f"  cpu={cpu_util:.1f}%" if cpu_util is not None else "  cpu=n/a"
    print(f"  recv={result['recv_mbps']} Mbps  loss={result['lost_percent']}%  jitter={result['jitter_ms']}ms{cpu_str}")
    return result


def print_table(results):
    hdr = f"{'Req (Mbps)':>10} {'Recv (Mbps)':>11} {'Loss (%)':>9} {'Jitter (ms)':>11} {'Pkts':>8} {'OOO':>5} {'CPU (%)':>8}"
    print("\n" + "=" * len(hdr))
    print("iperf3 UDP — QEMU qemu_virt_aarch64 — 1 stream, 1460 B")
    print("=" * len(hdr))
    print(hdr)
    print("-" * len(hdr))
    for r in results:
        if "error" in r:
            print(f"{r['requested_mbps']:>10}  ERROR")
        else:
            cpu_str = f"{r['cpu_util_pct']:>8.1f}" if r.get("cpu_util_pct") is not None else f"{'n/a':>8}"
            print(f"{r['requested_mbps']:>10} {r['recv_mbps']:>11.2f}"
                  f" {r['lost_percent']:>9.2f} {r['jitter_ms']:>11.4f}"
                  f" {r['total_packets']:>8} {r['out_of_order']:>5}{cpu_str}")
    print("=" * len(hdr))


def main():
    parser = argparse.ArgumentParser(description="iperf3_udp bandwidth sweep benchmark")
    parser.add_argument("--sdk",        default=DEFAULT_SDK)
    parser.add_argument("--board",      default=DEFAULT_BOARD)
    parser.add_argument("--bandwidths", default=",".join(map(str, BANDWIDTHS)))
    args = parser.parse_args()

    sdk = os.path.abspath(args.sdk)
    bandwidths = [int(b) for b in args.bandwidths.split(",")]

    print(f"SDK:   {sdk}")
    print(f"Board: {args.board}")
    print(f"BW:    {bandwidths} Mbps")

    print("\nInitial clean build...")
    run_make(["make", "clean", f"MICROKIT_BOARD={args.board}", f"MICROKIT_SDK={sdk}"], check=False)
    r = run_make(
        ["make", f"TARGET_BW_MBPS={bandwidths[0]}", "MICROKIT_CONFIG=benchmark",
         f"MICROKIT_BOARD={args.board}", f"MICROKIT_SDK={sdk}"],
        check=False
    )
    if r.returncode != 0:
        print(f"Initial build failed:\n{r.stderr[-1000:]}")
        sys.exit(1)
    print("Initial build OK")

    results = []
    for bw in bandwidths:
        r = benchmark_one(bw, sdk, args.board)
        if r:
            results.append(r)

    out_file = os.path.join(EXAMPLE_DIR, "benchmark_results.json")
    with open(out_file, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out_file}")
    print_table(results)


if __name__ == "__main__":
    main()
