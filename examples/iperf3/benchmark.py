#!/usr/bin/env python3
"""
iperf3 TCP benchmark — sweeps requested bandwidth 100–1000 Mbps (1 stream).
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

EXAMPLE_DIR  = os.path.dirname(os.path.abspath(__file__))
DEFAULT_SDK  = os.path.join(EXAMPLE_DIR, "../../microkit-sdk-2.1.0")
DEFAULT_BOARD = "qemu_virt_aarch64"
PORT = 5202
SERVER_IP = "192.168.64.1"
BANDWIDTHS = [100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]

QEMU_ARCH_ARGS = [
    "-machine", "virt,virtualization=on",
    "-cpu", "cortex-a53",
    "-m", "size=2G",
    "-serial", "mon:stdio",
]


def run_make(args, cwd=None, check=True):
    return subprocess.run(
        args, cwd=cwd or EXAMPLE_DIR,
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
    image = os.path.join(EXAMPLE_DIR, "build", "loader.img")
    print(f"\n=== {bw_mbps} Mbps ===")

    # Touch ctrl source to force recompile with new bitrate/tick_byte_limit
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

    qemu_cmd = (
        ["qemu-system-aarch64"]
        + QEMU_ARCH_ARGS
        + [
            "-device", f"loader,file={image},addr=0x70000000,cpu-num=0",
            "-nographic",
            "-device", "virtio-net-device,netdev=netdev0",
            "-netdev", f"user,id=netdev0,net=192.168.64.0/24,host={SERVER_IP}",
            "-global", "virtio-mmio.force-legacy=false",
            "-d", "guest_errors",
            "-smp", "4",
        ]
    )
    qemu = subprocess.Popen(
        qemu_cmd,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        start_new_session=True
    )
    qemu_lines = []
    qemu_reader = threading.Thread(
        target=lambda: qemu_lines.extend(collect_qemu_lines(qemu)),
        daemon=True
    )
    qemu_reader.start()

    # TCP test is 10s + protocol overhead; give 50s
    timeout_s = 50
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
    ss = end.get("sum_sent") or {}
    seconds = sr.get("seconds", 10)
    cpu_util = parse_cpu_util(qemu_lines)

    result = {
        "requested_mbps": bw_mbps,
        "recv_mbps":      round(sr.get("bits_per_second", 0) / 1e6, 2),
        "send_mbps":      round(ss.get("bits_per_second", 0) / 1e6, 2),
        "retransmits":    ss.get("retransmits", 0),
        "bytes_received": sr.get("bytes", 0),
        "seconds":        round(seconds, 2),
        "cpu_util_pct":   cpu_util,
    }
    cpu_str = f"  cpu={cpu_util:.1f}%" if cpu_util is not None else "  cpu=n/a"
    print(f"  recv={result['recv_mbps']} Mbps  retrans={result['retransmits']}{cpu_str}")
    return result


def print_table(results):
    hdr = f"{'Req (Mbps)':>10} {'Recv (Mbps)':>11} {'Send (Mbps)':>11} {'Retrans':>8} {'CPU (%)':>8}"
    print("\n" + "=" * len(hdr))
    print("iperf3 TCP — QEMU qemu_virt_aarch64 — 1 stream")
    print("=" * len(hdr))
    print(hdr)
    print("-" * len(hdr))
    for r in results:
        if "error" in r:
            print(f"{r['requested_mbps']:>10}  ERROR")
        else:
            cpu_str = f"{r['cpu_util_pct']:>8.1f}" if r.get("cpu_util_pct") is not None else f"{'n/a':>8}"
            print(f"{r['requested_mbps']:>10} {r['recv_mbps']:>11.2f}"
                  f" {r['send_mbps']:>11.2f} {r['retransmits']:>8}{cpu_str}")
    print("=" * len(hdr))


def main():
    parser = argparse.ArgumentParser(description="iperf3 TCP bandwidth sweep benchmark")
    parser.add_argument("--sdk",        default=DEFAULT_SDK)
    parser.add_argument("--board",      default=DEFAULT_BOARD)
    parser.add_argument("--bandwidths", default=",".join(map(str, BANDWIDTHS)))
    args = parser.parse_args()

    sdk = os.path.abspath(args.sdk)
    bandwidths = [int(b) for b in args.bandwidths.split(",")]

    print(f"SDK:   {sdk}")
    print(f"Board: {args.board}")
    print(f"BW:    {bandwidths} Mbps")
    print(f"Server: {SERVER_IP}:{PORT}")

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
