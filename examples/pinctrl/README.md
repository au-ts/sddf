<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Pinctrl example

This is a copy of the serial example with pinctrl incoporated to demonstrate how the pinctrl
subsystem can be minimally incorporated.

There's a pinctrl driver running at the highest priority to program all the registers value read
from the device tree before any other device drivers (at a lower priority) can run.

## Building

The following platforms are supported:
* imx8mm_evk
* imx8mp_evk
* imx8mq_evk
* maaxboard

For further details on building and running this example, please see the serial example.

For further details on the pinctrl driver, please see [pinctrl.md](../../docs/pinctrl/pinctrl.md)
