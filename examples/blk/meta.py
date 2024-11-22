import argparse
from sdfgen import SystemDescription, ProtectionDomain, Sddf, DeviceTree, LionsOS, Channel

PLATFORMS = [
    {
        "name": "qemu_virt_aarch64",
        "arch": 1,
        "paddr_top": 0xa_000_000,
        "blk_device_node": "virtio_mmio@a003e00",
    }
]

def generate_sdf(sdf):
    blk_driver = ProtectionDomain("blk_driver", "blk_driver.elf", priority=200)
    blk_virt = ProtectionDomain("blk_virt", "blk_virt.elf", priority=199)
    client = ProtectionDomain("client", "client.elf", priority=1)

    blk_node = dtb.node(platform["blk_device_node"])
    assert blk_node is not None

    blk_system = Sddf.Block(sdf, blk_node, blk_driver, blk_virt)
    blk_system.add_client(client)

    pds = [
        blk_driver,
        blk_virt,
        client
    ]
    for pd in pds:
        sdf.add_pd(pd)

    blk_system.connect()

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

    generate_sdf(sdf)
