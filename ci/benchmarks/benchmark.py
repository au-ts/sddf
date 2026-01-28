#!/usr/bin/env python3

import argparse
import datetime as dt
import socket
import subprocess
from pathlib import Path

IPBENCHD_PORT = 8036
udp_packet_size_default = 1472
tcp_packet_size_default = 1460

def abort_clients(clients: list[str]):
    for client in clients:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((client, IPBENCHD_PORT))
        sock.send(b"ABORT\n")
        sock.shutdown(socket.SHUT_WR)
        while True:
            data = sock.recv(4096)
            if not data:
                break
            print(data)
        sock.close()


def run_benchmark(args, throughput: int, packet_size: int):
    argv = [
        "ipbench",
        "--debug",
    ]

    make_arg_list = lambda **opts: ",".join(f"{k}={v}" for k, v in opts.items())

    # test mode
    argv += [
        "--test",
        "latency",
        "--test-args",
        make_arg_list(
            socktype=args.protocol,
            bps=throughput // len(args.clients),
            size=packet_size,
            warmup=args.warmup_seconds,
            cooldown=args.cooldown_seconds,
            samples=args.samples // len(args.clients),
        ),
    ]

    # remote clients
    argv += ["--port", str(IPBENCHD_PORT)]
    for client in args.clients:
        argv += ["--client", client]

    # device under test
    argv += [
        # echo server port
        "--test-target",
        args.ip,
        "--test-port",
        {
            "tcp": "1237",
            "udp": "1235",
        }[args.protocol],
        # benchmark stuff
        "--target-test",
        "cpu_target_lukem",
        "--target-test-hostname",
        args.ip,
        "--target-test-port",
        "1236",
    ]

    p = subprocess.run(argv, stdout=subprocess.PIPE)
    p.check_returncode()

    return p.stdout.decode("utf-8").replace("\n", "")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("ip", help="IP address of machine to benchmark")

    parser.add_argument(
        "--clients",
        nargs="+",
        default=["vb04", "vb05", "vb06", "vb07"],
    )
    parser.add_argument(
        "--udp",
        action="store_const",
        dest="protocol",
        const="udp",
        default="udp",
    )
    parser.add_argument(
        "--tcp",
        action="store_const",
        dest="protocol",
        const="tcp",
    )
    parser.add_argument(
        "--warmup-seconds",
        type=int,
        default=10,
    )
    parser.add_argument(
        "--cooldown-seconds",
        type=int,
        default=10,
    )
    parser.add_argument(
        "--samples",
        type=int,
        default=200_000,
    )
    parser.add_argument(
        "--packet-sizes",
        nargs="+",
        type=int,
    )
    parser.add_argument(
        "--throughputs",
        nargs="+",
        type=int,
        required=True,
    )

    return parser.parse_args()


if __name__ == "__main__":
    args = parse_args()

    packet_sizes = args.packet_sizes
    if not packet_sizes:
        default = udp_packet_size_default
        if args.protocol == "tcp":
            default = tcp_packet_size_default
        packet_sizes = [default]

    abort_clients(args.clients)
    abort_clients(args.clients)

    file = dt.datetime.now().strftime("output-%Y-%m-%dT%H:%M:%S.csv")

    output_link = Path("output.csv")
    if output_link.is_symlink():
        output_link.unlink()
        output_link.symlink_to(file)

    heading = "Requested_Throughput,Receive_Throughput,Send_Throughput,Packet_Size,Minimum_RTT,Average_RTT,Maximum_RTT,Stdev_RTT,Median_RTT,Bad_Packets,Idle_Cycles,Total_Cycles\n"

    data = ""
    with open(file, "w") as data_out:
        data_out.write(heading)
        data += heading

        try:
            for packet_size in packet_sizes:
                for throughput in args.throughputs:
                    row = run_benchmark(args, throughput, packet_size) + "\n"

                    data_out.write(row)
                    data += row
                    print(heading, row)

        finally:
            abort_clients(args.clients)

        print("Result Summary:")
        print(data)
