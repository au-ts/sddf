cd build
qemu-system-x86_64 -machine q35 -kernel /home/cheng/work/microkit/release/microkit-sdk-2.1.0-dev/board/x86_64_generic/debug/elf/sel4_32.elf -m size=2G -serial mon:stdio -cpu qemu64,+fsgsbase,+pdpe1gb,+pcid,+invpcid,+xsave,+xsaves,+xsaveopt -initrd loader.img -device intel-iommu,intremap=on,caching-mode=on -device virtio-blk-pci,drive=hd,addr=0x3.0,iommu_platform=on,disable-legacy=on \
-nographic \
-d guest_errors \
-drive file=disk,if=none,format=raw,id=hd