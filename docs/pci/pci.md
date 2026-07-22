<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# sDDF PCIe Subsystem

The Enhanced Configuration Access Method (ECAM) space is the interface for 
software to negotiate the PCIe-related settings, such as memory BARs and IRQs.
Giving the device drivers the access to ECAM apparently breaks the isolation
principle, as they would be able to mess things up.

The solution is to have PCIe driver as a centralised server that address all
the requests from the device drivers and set things up for them. The simplified
implementation of this mechanism is to patch the requests to the PCIe driver at
build time, so the PCIe driver can allocates and configures resources for them
once it receives the available resource window from the ACPI driver.

## Progress

The PCIe driver is currently in an experimental phase, which has proved the
feasibility of dynamically allocating and mapping IRQs and memroy for PCIe
device drivers, so the PCIe device drivers will have required resources ready 
when they are scheduled.

## TODO

- [ ] Resource requests patched by metaprogram for PCIe device drivers
- [ ] Centralised MSI/MSI-X interrupt management
- [ ] Separate IRQ node for restricted access to PCIe device driver's CSpace
- [ ] Work as a post-initialiser
