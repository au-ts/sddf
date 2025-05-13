<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Pinctrl example

This is a copy of the serial example with pinctrl incoporated to demo what you need to use the pinctrl subsystem in a minimal manner.

There's a pinctrl driver running at the highest priority to program all the registers value set in the device tree before any other device drivers (at a lower priority) can run.

## Building

The following platforms are supported:
* imx8mm_evk
* imx8mp_evk
* imx8mq_evk
* maaxboard

For further details on building and running this example, please see the serial example.
