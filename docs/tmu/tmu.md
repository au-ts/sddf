<!--
    Copyright 2026, UNSW
    SPDX-License-Identifier: BSD-2-Clause
-->

# TMU sub-system

The sDDF has support for thermal monitoring units: simple peripherals used to manage the
temperature of an SoC and generate interrupts when certain trip points are reached.

The TMU sub-system consists of a driver only which is connected to clients with a channel. All
operations are client-initiated PPCs, except for a special IRQ forwarding function which
permits the driver to notify a certain client (e.g. a thermal controller client) when a
threshold interrupt is emitted.

## Protocol

```c
typedef enum {
    SDDF_TMU_SET_IRQ_MODE,
    SDDF_TMU_SET_IRQ_THRESHOLD,
    SDDF_TMU_GET_TEMP
} sddf_tmu_ppc_codes_t;
```

There are three protected calls that clients may make, two of which are reserved for a "controller"
client.

## Controller client

The TMU class may designate up to one client as a controller, granting it privileges to set
the temperature threshold IRQ, change IRQ modes and have IRQs forwarded to it as notifications.

**IMPORTANT**: we cannot use these interrupts on the `imx` boards without also reprogramming the
system management Cortex-M processor on board - by default, the system management chip will shut
off the board if an IRQ is received.

The controller client is specified using Acacia: set `is_controller` to `True` when adding the
client.

### Interrupt forwarding

IRQ forwarding is will be automatically enabled if there is a controller client, unless disabled
when instantiating the TMU subsystem in Acacia. The client will receive
a notification from the driver when IRQs of any type are triggered.

IRQ forwarding can be disabled by setting `sDDFTMU.__init__()`'s `allow_irq_fwd` kwarg to `False`.
This will not affect the other functionality afforded to the controller.

### Client PPCs

(see `include/sddf/tmu/protocol.h`)

#### SDDF_TMU_SET_IRQ_MODE

Set the interrupt mode to one of the following:
```c
typedef enum {
    SDDF_TMU_IRQ_MODE_DISABLED,
    SDDF_TMU_IRQ_MODE_INSTANTANEOUS,    // IRQ on instant of threshold exceeding
    SDDF_TMU_IRQ_MODE_AVG,   // IRQ when low-passed average exceeds theshold
    SDDF_TMU_IRQ_MODES_NUM
} sddf_tmu_irq_modes_t;
```

Using `client.h`, call:
```c
int sddf_tmu_set_irq_mode(microkit_channel channel, sddf_tmu_irq_modes_t mode)
```

#### SDDF_TMU_SET_IRQ_THESHOLD

Program the configurable interrupt to trip at a certain temperature in degrees celsius
(`sddf_temp_celsius_t`).

Using `client.h`, call:
```c
int sddf_tmu_set_irq_threshold(microkit_channel channel, sddf_temp_celsius_t threshold)
```

#### SDDF_TMU_GET_TEMP

Get the current temperature information. Returns a `sddf_tmu_temp_info_t` containing the
current instantaneous and average temperatures + validity markers for each.

Temperatures and validity markers are identical to what is emitted by hardware.
Using `client.h`, call:
```c
int sddf_tmu_get_temp(microkit_channel channel, sddf_tmu_temp_info_t *info)
```
