<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# GenMC
[GenMC](https://github.com/MPI-SWS/genmc) is a model checker for verifying concurrent C programs.
GenMC works by efficiently enumerating the state space of the concurrent system, which makes testing
concurrent programs reliable and reproducible.
We use it to verify partial correctness of implementations of critical concurrent data structures,
some of our lock-free single-producer single-consumer queue, currently just the queue implementation
used by the serial subsystem.

## Usage
Follows the instruction of GenMC to install the tool, then run
```bash
bash ci/genmc/genmc.sh
```

## Limitations
GenMC does not target infinite programs. Verifying non-terminating programs under weak memory models
is an open research problem. We also assume that the address space has been properly set up.

## Trusted Computing Base
We assume the correctness of GenMC. In addition, GenMC supports the release-acquire subset of the
C11 memory model, which usually targets multi-threaded applications under the same address space.
We assume the same setting applies to sddf on supported platforms, even though different protection
domains have different address spaces.
