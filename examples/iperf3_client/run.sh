#!/bin/sh
# Convenience launcher so you never have to paste the long make line.
#
# Usage:
#   ./run.sh <single|two|four> [tcp|udp] [num_streams]
#
# Examples:
#   ./run.sh four tcp        # 2 clients, 4 cores, TCP
#   ./run.sh single udp      # 1 client, 1 core, UDP
#   ./run.sh two tcp 5       # 1 client, 2 cores, TCP, 5 parallel streams
#
# Override the SDK/board via env if needed:
#   MICROKIT_SDK=/path ./run.sh four tcp
set -e

BOARD="${MICROKIT_BOARD:-qemu_virt_aarch64}"
SDK="${MICROKIT_SDK:-/Users/lululululluke/sddf/microkit-sdk-2.1.0}"

CFG="$1"
PROTO="${2:-tcp}"
NS="${3:-1}"

case "$CFG" in
    single) SMP=single_core; MK=benchmark;     CLIENTS=1 ;;
    two)    SMP=two_core;    MK=smp-benchmark;  CLIENTS=1 ;;
    four)   SMP=four_core;   MK=smp-benchmark;  CLIENTS=2 ;;
    *) echo "usage: $0 <single|two|four> [tcp|udp] [num_streams]"; exit 1 ;;
esac

echo "=================================================================="
echo " config=$SMP  protocol=$PROTO  streams=$NS  kernel=$MK  clients=$CLIENTS"
echo " Start these iperf3 server(s) FIRST, each in its own terminal:"
i=0
while [ "$i" -lt "$CLIENTS" ]; do
    echo "     iperf3 -s -p $((5202 + i))"
    i=$((i + 1))
done
echo "=================================================================="

cd "$(dirname "$0")"
make clean MICROKIT_BOARD="$BOARD" MICROKIT_SDK="$SDK"
make qemu  MICROKIT_BOARD="$BOARD" MICROKIT_SDK="$SDK" \
    PROTOCOL="$PROTO" NUM_STREAMS="$NS" \
    MICROKIT_CONFIG="$MK" SMP_CONFIG="core_config/${SMP}.json"
