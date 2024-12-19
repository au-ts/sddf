import argparse
import struct
from typing import Dict, List, Any, Tuple
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map
Channel = SystemDescription.Channel

class Platform:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, serial: str, timer: str, ethernet: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.serial = serial
        self.timer = timer
        self.ethernet = ethernet

PLATFORMS: List[Platform] = [
    Platform("qemu_virt_aarch64", SystemDescription.Arch.AARCH64, 0x6_0000_000, "pl011@9000000", "timer", "virtio_mmio@a003e00"),
    Platform("odroidc4", SystemDescription.Arch.AARCH64, 0x60000000, "soc/bus@ff800000/serial@3000", "soc/bus@ffd00000/watchdog@f0d0", "soc/ethernet@ff3f0000"),
    Platform("maaxboard", SystemDescription.Arch.AARCH64, 0x70000000, "soc@0/bus@30800000/serial@30860000", "soc@0/bus@30000000/timer@302d0000", "soc@0/bus@30800000/ethernet@30be0000"),
    Platform("imx8mm_evk", SystemDescription.Arch.AARCH64, 0x70000000, "soc@0/bus@30800000/spba-bus@30800000/serial@30890000", "soc@0/bus@30000000/timer@302d0000", "soc@0/bus@30800000/ethernet@30be0000"),
    Platform("imx8mp_evk", SystemDescription.Arch.AARCH64, 0x70000000, "soc@0/bus@30800000/spba-bus@30800000/serial@30860000", "soc@0/bus@30000000/timer@302d0000", "soc@0/bus@30800000/ethernet@30be0000"),
    Platform("imx8mq_evk", SystemDescription.Arch.AARCH64, 0x70000000, "soc@0/bus@30800000/serial@30860000", "soc@0/bus@30000000/timer@302d0000", "soc@0/bus@30800000/ethernet@30be0000"),
]

"""
Below are classes to serialise into custom configuration for the benchmarking component.
All serialised definitions are little endian and pointers are 64-bit integers.
"""

class BenchmarkIdleConfig:
    def __init__(self, cycle_counters: int, ch_init: int):
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


class BenchmarkClientConfig:
    def __init__(self, cycle_counters: int, ch_start: int, ch_stop: int):
        self.cycle_counters = cycle_counters
        self.ch_start = ch_start
        self.ch_stop = ch_stop

    '''
        Matches struct definition:
        {
            void *;
            uint8_t;
            uint8_t;
        }
    '''
    def serialise(self) -> bytes:
        return struct.pack("<qBB", self.cycle_counters, self.ch_start, self.ch_stop)


class BenchmarkConfig:
    def __init__(self, ch_start: int, ch_stop: int, ch_init: int, children: List[Tuple[int, str]]):
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.ch_init = ch_init
        self.children = children


    def serialise(self) -> bytes:
        child_config_format = "c" * 65
        pack_str = "<BBBB" + child_config_format * 64
        child_bytes = bytearray()
        for child in self.children:
            c_name = child[1].encode("utf-8")
            c_name_padded = c_name.ljust(64, b'\0')
            assert len(c_name_padded) == 64
            child_bytes.extend(c_name_padded)
            child_bytes.extend(child[0].to_bytes(1, "little"))

        child_bytes = child_bytes.ljust(64 * 65, b'\0')

        child_bytes = [x.to_bytes(1, "little") for x in child_bytes]

        return struct.pack(pack_str, self.ch_start, self.ch_stop, self.ch_init, len(self.children), *child_bytes)


def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    uart_node = dtb.node(platform.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(platform.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(platform.timer)
    assert uart_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf", priority=101)
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("uart_driver", "uart_driver.elf", priority=100)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=99)
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    ethernet_driver = ProtectionDomain("ethernet_driver", "eth_driver.elf", priority=101, budget=100, period=400)
    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf", priority=100, budget=20000)
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf", priority=99)
    net_system = Sddf.Network(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    client0 = ProtectionDomain("client0", "lwip0.elf", priority=97, budget=20000)
    client0_net_copier = ProtectionDomain("client0_net_copier", "network_copy0.elf", priority=98, budget=20000)
    client1 = ProtectionDomain("client1", "lwip1.elf", priority=97, budget=20000)
    client1_net_copier = ProtectionDomain("client1_net_copier", "network_copy1.elf", priority=98, budget=20000)

    serial_system.add_client(client0)
    serial_system.add_client(client1)
    timer_system.add_client(client0)
    timer_system.add_client(client1)
    net_system.add_client_with_copier(client0, client0_net_copier, mac_addr="52:54:01:00:00:05")
    net_system.add_client_with_copier(client1, client1_net_copier, mac_addr="52:54:01:00:00:06")

    # Benchmark specific resources

    bench_idle = ProtectionDomain("bench_idle", "idle.elf", priority=1)
    bench = ProtectionDomain("bench", "benchmark.elf", priority=254)

    serial_system.add_client(bench)

    benchmark_pds = [
        uart_driver,
        serial_virt_tx,
        ethernet_driver,
        net_virt_tx,
        net_virt_rx,
        client0,
        client0_net_copier,
        client1,
        client1_net_copier,
        timer_driver,
    ]
    pds = [
        bench_idle,
        bench,
    ]
    bench_children = []
    for pd in benchmark_pds:
        child_id = bench.add_child_pd(pd)
        bench_children.append((child_id, pd.name))
    for pd in pds:
        sdf.add_pd(pd)

    # Benchmark START channel
    bench_start_ch = Channel(client0, bench)
    sdf.add_channel(bench_start_ch)
    # Benchmark STOP channel
    bench_stop_ch = Channel(client0, bench)
    sdf.add_channel(bench_stop_ch)

    bench_idle_ch = Channel(bench_idle, bench)
    sdf.add_channel(bench_idle_ch)

    cycle_counters_mr = MemoryRegion("cycle_counters", 0x1000)
    sdf.add_mr(cycle_counters_mr)

    bench_idle.add_map(Map(cycle_counters_mr, 0x5_000_000, perms=Map.Perms(r=True, w=True)))
    client0.add_map(Map(cycle_counters_mr, 0x20_000_000, perms=Map.Perms(r=True, w=True)))
    bench_idle_config = BenchmarkIdleConfig(0x5_000_000, bench_idle_ch.pd_a_id)

    bench_client_config = BenchmarkClientConfig(0x20_000_000, bench_start_ch.pd_a_id, bench_stop_ch.pd_a_id)

    benchmark_config = BenchmarkConfig(bench_start_ch.pd_b_id, bench_stop_ch.pd_b_id, bench_idle_ch.pd_b_id, bench_children)

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

    with open(f"{output_dir}/benchmark_config.data", "wb+") as f:
        f.write(benchmark_config.serialise())

    with open(f"{output_dir}/benchmark_idle_config.data", "wb+") as f:
        f.write(bench_idle_config.serialise())

    with open(f"{output_dir}/benchmark_client_config.data", "wb+") as f:
        f.write(bench_client_config.serialise())

    with open(f"{output_dir}/{sdf_file}", "w+") as f:
        f.write(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtbs", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--platform", required=True, choices=[p.name for p in PLATFORMS])
    parser.add_argument("--output", required=True)
    parser.add_argument("--sdf", required=True)

    args = parser.parse_args()

    platform = next(filter(lambda p: p.name == args.platform, PLATFORMS))

    sdf = SystemDescription(platform.arch, platform.paddr_top)
    sddf = Sddf(args.sddf)

    with open(args.dtbs + f"/{platform.name}.dtb", "rb") as f:
        dtb = DeviceTree(f.read())

    generate(args.sdf, args.output, dtb)
