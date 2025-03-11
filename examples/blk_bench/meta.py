# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
import argparse
import struct
from typing import List, Tuple
from dataclasses import dataclass
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel

@dataclass
class Board:
    name: str
    arch: SystemDescription.Arch
    paddr_top: int
    # Default partition if the user has not specified one
    partition: int
    blk: str
    serial: str
    timer: str


BOARDS: List[Board] = [
    Board(
        name="qemu_virt_aarch64",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x60_000_000,
        partition=0,
        blk="virtio_mmio@a003e00",
        serial="pl011@9000000",
        timer="timer",
    ),
    Board(
        name="maaxboard",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x70_000_000,
        partition=2,
        blk="soc@0/bus@30800000/mmc@30b40000",
        serial="soc@0/bus@30800000/serial@30860000",
        timer="soc@0/bus@30000000/timer@302d0000",
    ),
    Board(
        name="odroidc4",
        arch=SystemDescription.Arch.AARCH64,
        paddr_top=0x80_000_000,
        partition=0,
        blk="soc/sd@ffe05000",
        serial="soc/bus@ff800000/serial@3000",
        timer="soc/bus@ffd00000/watchdog@f0d0",
    ),
    # TODO: Need to add a driver for google,goldfish rtc
    #Board(
    #    name="qemu_virt_riscv64",
    #    arch=SystemDescription.Arch.RISCV64,
    #    paddr_top=0xa0_000_000,
    #    partition=0,
    #    blk="soc/virtio_mmio@10008000",
    #    serial="soc/virtio_mmio@10008000"
    #    timer="soc/rtc@101000",
    #),
]

"""
Below are classes to serialise into custom configuration for the benchmarking component.
All serialised definitions are little endian and pointers are 64-bit integers.
"""

class BenchmarkIdleConfig:
    def __init__(self, cycle_counters: int, ch_init: int):
        """
        cycle_counters: virtual address of MemoryRegion containing cycle_counters bench struct.
        ch_init: channel id for initialisting the idle thread.
        """
        self.cycle_counters = cycle_counters
        self.ch_init = ch_init

    '''
        Matches struct definition:
        {
            void *;
            uint8_t;
        }
    '''
    def serialise(self) -> bytes:
        return struct.pack("<qc", self.cycle_counters, self.ch_init.to_bytes(1, "little"))


class BenchmarkBlkClientConfig:
    def __init__(self, ch_start: int, ch_stop: int, ch_bench_run: int):
        """
        ch_start: channel id for notifying the benchmarking pd to start pmu counters.
        ch_stop: channel id for notifying the benchmarking pd to stop pmu counters.
        ch_bench_run: channel id for receiving notification from benchmarking pd to begin the next benchmark run.
        """
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.ch_bench_run = ch_bench_run

    '''
        Matches struct definition:
        {
            uint8_t;
            uint8_t;
            uint8_t;
        }
    '''
    def serialise(self) -> bytes:
        return struct.pack("<BBB", self.ch_start, self.ch_stop, self.ch_bench_run)


class BenchmarkBlkConfig:
    def __init__(self, ch_start: int, ch_stop: int, ch_bench_run: int, ch_init: int, children: List[Tuple[int, str]]):
        """
        ch_start: channel id for receiving notification from client pd to start pmu counters.
        ch_stop: channel id for receiving notification from client pd to stop pmu counters.
        ch_bench_run: channel id for notifying client pd to begin the next benchmark run.
        ch_init: channel id to notify idle pd to initialise its busy loop.
        children: list of (int, str) tuples, matching PD ID with a string name. (Used e.g. for printing fault info)
        """
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.ch_bench_run = ch_bench_run
        self.ch_init = ch_init
        self.children = children

    def serialise(self) -> bytes:
        child_config_format = "c" * 65
        pack_str = "<BBBBB" + child_config_format * 64
        child_bytes = bytearray()
        for child in self.children:
            c_name = child[1].encode("utf-8")
            c_name_padded = c_name.ljust(64, b'\0')
            assert len(c_name_padded) == 64
            child_bytes.extend(c_name_padded)
            child_bytes.extend(child[0].to_bytes(1, "little"))

        child_bytes = child_bytes.ljust(64 * 65, b'\0')

        child_bytes_list = [x.to_bytes(1, "little") for x in child_bytes]

        return struct.pack(
            pack_str, self.ch_start, self.ch_stop, self.ch_bench_run,
            self.ch_init, len(self.children), *child_bytes_list
        )


def generate(sdf_file: str, output_dir: str, sdf: SystemDescription, dtb: DeviceTree, board: Board):
    uart_node = dtb.node(board.serial)
    assert uart_node is not None
    blk_node = dtb.node(board.blk)
    assert blk_node is not None
    timer_node = dtb.node(board.timer)
    assert timer_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=254)
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=254)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=253)

    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    client = ProtectionDomain("client", "client.elf", priority=98)
    # XXX: figure out stack size for below
    blk_virt = ProtectionDomain("blk_virt", "blk_virt.elf", priority=100, stack_size=0x2000)

    blk_driver = ProtectionDomain("blk_driver", "blk_driver.elf", priority=102)
    blk_system = Sddf.Blk(sdf, blk_node, blk_driver, blk_virt)
    partition = int(args.partition) if args.partition else board.partition
    blk_system.add_client(client, partition=partition, queue_capacity=1024, data_size=10*1024*1024)
    if board.name == "odroidc4":
        gpio_mr = MemoryRegion("gpio", 0x1000, paddr=0xff800000)
        blk_driver.add_map(Map(gpio_mr, 0xff800000, perms="rw", cached=False))
        sdf.add_mr(gpio_mr)

    bench_idle = ProtectionDomain("bench_idle", "idle.elf", priority=1)
    bench = ProtectionDomain("bench", "benchmark_blk.elf", priority=103)

    serial_system.add_client(bench)
    serial_system.add_client(client)

    # Only add channel timer->blk_driver for those drivers that need it.
    if board.name == "maaxboard":
        timer_system.add_client(blk_driver)
    timer_system.add_client(client)
    timer_system.add_client(bench)

    benchmark_pds = [
            uart_driver,
            serial_virt_tx,
            blk_driver,
            blk_virt,
            client,
            timer_driver,
            bench_idle,
            ]

    pds = [
            bench,
            ]

    bench_children = []
    for pd in benchmark_pds:
        child_id = bench.add_child_pd(pd)
        bench_children.append((child_id, pd.name))
    for pd in pds:
        sdf.add_pd(pd)

    #def __init__(self, ch_start: int, ch_stop: int, ch_bench_run: int, ch_init: int, children: List[Tuple[int, str]]):
    # Benchmark START channel
    bench_start_ch = Channel(client, bench)
    sdf.add_channel(bench_start_ch)
    # Benchmark STOP channel
    bench_stop_ch = Channel(client, bench)
    sdf.add_channel(bench_stop_ch)
    # Benchmark BENCH_RUN channel
    bench_run_ch = Channel(client, bench)
    sdf.add_channel(bench_run_ch)
    # Benchmark Idle PD INIT channel
    bench_idle_ch = Channel(bench_idle, bench)
    sdf.add_channel(bench_idle_ch)

    cycle_counters_mr = MemoryRegion("cycle_counters", 0x1000)
    sdf.add_mr(cycle_counters_mr)

    bench_idle.add_map(Map(cycle_counters_mr, 0x5_000_000, perms="rw"))
    benchmark_idle_config = BenchmarkIdleConfig(0x5_000_000, bench_idle_ch.pd_a_id)

    benchmark_blk_client_config = BenchmarkBlkClientConfig(
            bench_start_ch.pd_a_id,
            bench_stop_ch.pd_a_id,
            bench_run_ch.pd_a_id
            )

    benchmark_blk_config = BenchmarkBlkConfig(
            bench_start_ch.pd_b_id,
            bench_stop_ch.pd_b_id,
            bench_run_ch.pd_b_id,
            bench_idle_ch.pd_b_id,
            bench_children
            )

    assert blk_system.connect()
    assert blk_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)
    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)

    with open(f"{output_dir}/benchmark_blk_config.data", "wb+") as f:
        f.write(benchmark_blk_config.serialise())
    with open(f"{output_dir}/benchmark_idle_config.data", "wb+") as f:
        f.write(benchmark_idle_config.serialise())
    with open(f"{output_dir}/benchmark_blk_client_config.data", "wb+") as f:
        f.write(benchmark_blk_client_config.serialise())
    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.render())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtb", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--board", required=True, choices=[b.name for b in BOARDS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)
    parser.add_argument("--partition")

    args = parser.parse_args()

    board = next(filter(lambda b: b.name == args.board, BOARDS))

    sdf = SystemDescription(board.arch, board.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtb, "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, sdf, dtb, board)
