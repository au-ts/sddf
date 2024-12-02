import argparse
from sdfgen import SystemDescription, ProtectionDomain, Sddf, DeviceTree

PLATFORMS = [
    {
        "name": "qemu_virt_aarch64",
        "arch": 1,
        "paddr_top": 0xa_000_000,
        "serial_device_node": "pl011@9000000",
    },
    {
        "name": "odroidc4",
        "arch": 1,
        "paddr_top": 0x80000000,
        "serial_device_node": "soc/bus@ff800000/serial@3000",
    },
    {
        "name": "maaxboard",
        "arch": 1,
        "paddr_top": 0xa0000000,
        "serial_device_node": "soc@0/bus@30800000/serial@30860000",
    },
    {
        "name": "star64",
        "arch": 3,
        "paddr_top": 0x100000000,
        "serial_device_node": "soc/serial@10000000",
    },
]

def generate_sdf():
    serial_driver = ProtectionDomain("serial_driver", "serial_driver.elf", priority=200)
    serial_virt_tx = ProtectionDomain("serial_virt_tx", "serial_virt_tx.elf", priority=199)
    serial_virt_rx = ProtectionDomain("serial_virt_rx", "serial_virt_rx.elf", priority=199)
    client = ProtectionDomain("client", "client.elf", priority=1)

    serial_node = dtb.node(platform["serial_device_node"])
    assert serial_node is not None

    serial_system = Sddf.Serial(sdf, serial_node, serial_driver, serial_virt_tx, serial_virt_rx)
    serial_system.add_client(client)

    pds = [
        serial_driver,
        serial_virt_tx,
        serial_virt_rx,
        client,
    ]
    for pd in pds:
        sdf.add_pd(pd)

    serial_system.connect()

    print(sdf.xml())


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--dtbs", required=True)
    parser.add_argument("--sddf", required=True)
    parser.add_argument("--platform", required=True, choices=[p["name"] for p in PLATFORMS])

    args = parser.parse_args()

    platform = next(filter(lambda p: p["name"] == args.platform, PLATFORMS))
    platform_name = platform["name"]

    sdf = SystemDescription(platform["arch"], platform["paddr_top"])
    sddf = Sddf(args.sddf)

    with open(args.dtbs + f"/{platform_name}.dtb", "rb") as f:
        dtb = DeviceTree(f.read())

    generate_sdf()
