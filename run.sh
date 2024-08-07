#!/bin/sh

mkdir -p bin/EFI/BOOT/
mv $1 bin/EFI/BOOT/BOOTAA64.EFI

qemu-system-aarch64 \
  -M virt,gic-version=3,secure=off,virtualization=on \
  -smp 4 -bios /usr/share/qemu-efi-aarch64/QEMU_EFI.fd -cpu cortex-a53 -m 2G \
  -nographic -device virtio-blk-device,drive=disk \
  -drive file=fat:rw:bin/,format=raw,if=none,media=disk,id=disk \
  -cdrom ~/alpine-virt-3.20.2-aarch64.iso \
  -boot menu=on

  #  -smp 4 -bios QEMU_EFI.fd -cpu cortex-a53 -m 2G \
  #  , dumpdtb=qemu.dtb \\dtbを得るための処理