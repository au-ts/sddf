<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Timer Proof

This directory contains `timer_common.z3`, an smtlib model of `period_transform`,
the split-remainder routine used by `ticks_to_ns` and `ns_to_ticks` to convert
between tick counts and nanoseconds while avoiding integer division precision loss.

The proof can be checked with the [Z3 Theorem Prover](https://github.com/Z3Prover/z3):

```bash
z3 timer_common.z3
```
