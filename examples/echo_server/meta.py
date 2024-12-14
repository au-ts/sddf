import argparse
from typing import Dict, List, Any, Tuple
from sdfgen import SystemDescription, Sddf, DeviceTree

ProtectionDomain = SystemDescription.ProtectionDomain
MemoryRegion = SystemDescription.MemoryRegion
Map = SystemDescription.Map

class Platform:
    def __init__(self, name: str, arch: SystemDescription.Arch, paddr_top: int, serial: str, timer: str, ethernet: str):
        self.name = name
        self.arch = arch
        self.paddr_top = paddr_top
        self.serial = serial
        self.timer = timer
        self.ethernet = ethernet

# TODO: add QEMU virt RISC-V, i.MX8MM-EVK, i.MX8MQ-EVK, i.MX8MP-EVK
PLATFORMS: List[Platform] = [
    Platform("qemu_virt_aarch64", SystemDescription.Arch.AARCH64, 0x6_0000_000, "pl011@9000000", "timer", "virtio_mmio@a003e00"),
    Platform("odroidc4", SystemDescription.Arch.AARCH64, 0x40000000, "soc/bus@ff800000/serial@3000", "soc/bus@ffd00000/watchdog@f0d0", "soc/ethernet@ff3f0000"),
    # Platform("maaxboard", SystemDescription.Arch.AARCH64, 0xa_000_000, "soc@0/bus@30800000/serial@30860000"),
]

# Classes to serialise into custom configuration for the benchmarking
# component.
# All serialised definitions are little endian and pointers are 64-bit
# integers.

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
        struct.pack(">qc", self.cycle_counters, self.ch_init)


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
        return struct.pack(">qcc", self.cycle_counters, self.ch_start, self.ch_stop)


class BenchmarkConfig:
    def __init__(self, ch_start: int, ch_stop: int, ch_init: int, children: List[Tuple[int, str]]):
        self.ch_start = ch_start
        self.ch_stop = ch_stop
        self.ch_init = ch_init
        self.children = children


    def serialise(self) -> bytes:
        pack_str = ">cccq"
        for child in self.children:
            c_name = self.name.encode("utf-8")



def generate(sdf_file: str, output_dir: str, dtb: DeviceTree):
    uart_node = dtb.node(platform.serial)
    assert uart_node is not None
    ethernet_node = dtb.node(platform.ethernet)
    assert ethernet_node is not None
    timer_node = dtb.node(platform.timer)
    assert uart_node is not None

    timer_driver = ProtectionDomain("timer_driver", "timer_driver.elf")
    timer_system = Sddf.Timer(sdf, timer_node, timer_driver)

    uart_driver = ProtectionDomain("uart_driver", "uart_driver.elf", priority=200)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=199)
    serial_system = Sddf.Serial(sdf, uart_node, uart_driver, serial_virt_tx)

    ethernet_driver = ProtectionDomain("ethernet_driver", "eth_driver.elf")
    net_virt_tx = ProtectionDomain("net_virt_tx", "network_virt_tx.elf")
    net_virt_rx = ProtectionDomain("net_virt_rx", "network_virt_rx.elf")
    net_system = Sddf.Network(sdf, ethernet_node, ethernet_driver, net_virt_tx, net_virt_rx)

    client0 = ProtectionDomain("client0", "lwip0.elf", priority=1)
    client0_net_copier = ProtectionDomain("client0_net_copier", "network_copy0.elf", priority=1)
    client1 = ProtectionDomain("client1", "lwip1.elf", priority=1)
    client1_net_copier = ProtectionDomain("client1_net_copier", "network_copy1.elf", priority=1)

    serial_system.add_client(client0)
    serial_system.add_client(client1)
    timer_system.add_client(client0)
    timer_system.add_client(client1)
    net_system.add_client_with_copier(client0, client0_net_copier, mac_addr="0f:1f:2f:3f:4f:5f")
    net_system.add_client_with_copier(client1, client1_net_copier, mac_addr="0f:1f:2f:3f:4f:6f")

    # Benchmark specific resources

    bench_idle = ProtectionDomain("bench_idle", "idle.elf")
    bench = ProtectionDomain("bench", "benchmark.elf")

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
    # benchmark_children = []
    # for pd in benchmark_pds:
    #     child_id = bench.add_child_pd(pd)
    #     benchmark_children.append((child_id, pd.name))
    # for pd in pds:
        # sdf.add_pd(pd)
    for pd in benchmark_pds:
        sdf.add_pd(pd)

    # Need to add channels between benchmark and benchmark client

    assert serial_system.connect()
    assert serial_system.serialise_config(output_dir)
    assert net_system.connect()
    assert net_system.serialise_config(output_dir)
    assert timer_system.connect()
    assert timer_system.serialise_config(output_dir)

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
