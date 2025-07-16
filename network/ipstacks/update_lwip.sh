#!/usr/bin/env bash
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

set -euo pipefail

LWIP_VERSION="2.1.3"

wget --continue "https://download-mirror.savannah.gnu.org/releases/lwip/lwip-${LWIP_VERSION}.zip" -O "lwip.zip"

rm -rf lwip/
unzip lwip.zip
mv "lwip-${LWIP_VERSION}/" lwip/

find lwip/ -type f -print0 | xargs -0 dos2unix
rm -rf lwip/doc/doxygen/output/html/
rm lwip/pax_global_header

patch -p 1 < no-dhcp-arp-check.patch
