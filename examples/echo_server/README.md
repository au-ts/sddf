<!--
    Copyright 2024, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Network echo server

## Building
```sh
make BUILD_DIR=<path/to/build> MICROKIT_SDK=<path/to/sdk> MICROKIT_CONFIG=(benchmark/release/debug)
```

## Benchmarking

In order to run the benchmarks, set `MICROKIT_CONFIG=benchmark`. The system has
been designed to interact with [ipbench](https://sourceforge.net/projects/ipbench/)
to take measurements.

Checks to make before benchmarking:
* Turn off all debug prints.
* Run with LWIP asserts turned off as well (`LWIP_NOASSERT`).
* Make sure compiler optimisations are enabled.

## Pancake Note

This is one example of a serial driver written in pancake. The currently supporting board is `imx8mm_evk` and `maaxboard1` and `maaxboard2`.

The relavent files are:
```
sddf
├── drivers
│   └── network
│       └── imx
│           ├── ethernet_pnk.c
|           ├── ehternet_helper.🥞
│           └── ethernet.🥞
├── include
│   └── sddf
│       └── network
│           ├── queue.🥞
│           └── queue_helper.🥞
└── util
    ├── util.🥞
    └── pancake_ffi.c
```

### Build and run with pancake
1. Download the latest (green master) cakeml compiler from [cakeml regression](https://cakeml.org/regression.cgi/):
```
wget https://cakeml.org/regression/artefacts/version-number/cake-x64-64.tar.gz
tar -xzf
cd cake-x64-64/
make cake
```
2. Get the latest Microkit from https://github.com/seL4/microkit/releases
3. Build driver image: 
```
     make BUILD_DIR=$(pwd)/build                            \
     MICROKIT_SDK=/path/to/microkit-sdk                     \
     MICROKIT_CONFIG=benchmark                              \
     CAKE_COMPILER=cake                                     \
     PANCAKE_NW=driver                                      \
     MICROKIT_BOARD=maaxboard
```
4. Run with `build/loader.img` on your bare metal (or via TS machine queue)
