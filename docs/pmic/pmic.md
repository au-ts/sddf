<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# sDDF PMIC Subsystem

The sDDF has support for I²C-based PMIC devices, using the sDDF I²C driver as
supporting infrastructure.

## Power Management ICs

Many SoCs have an external **Power Management IC**
(PMIC) controlled via I2C. This is a chip that is responsible for feeding in
several power lines to the chip and controlling their output with an array of
regulators.

## PMIC driver class

**CURRENT STATUS**: the PMIC class is a WIP and only supports controlling the output voltage
of regulators in the `bd71837` driver. The protocol supports all operations, but they are
not implemented there as of the time of writing. This is sufficient for implementing
basic system management features like DVFS (dynamic voltage and frequency scaling).

A PMIC contains many programmable regulators, each generating a voltage rail for
various board functions.
Each regulator has different:
    - voltage output ranges (different minima and maxima),
    - ability to set a current limit, with different maxima and minima,
    - ability to be turned on or off, and
    - step sizes for configuring voltages and currents.

The PMIC driver must be able to deal with manipulating these heterogeneous
regulators programmatically because clients may generate requests
that are not possible to implement, or that conflict with the
requirements for other clients.

The core of the PMIC driver is a table of regulator descriptions, parameterised
by regulator IDs that are stored in a shared PMIC bindings header file for the
specific PMIC. The bindings header file is available to clients of the PMIC
driver as a way to identify specific regulators. The regulator description
table encodes all capabilities of every register such that our driver can
return descriptive errors for incorrect requests and avoid unnecessary I²C
operations.

The PMIC protocol provides a \emph{Protected Procedure Call} (PPC) interface to
clients, with the following methods available:
- Enable or disable a target regulator,
- Set the output voltage of a regulator,
- Set the current limit of a regulator,
- Get info about the state of a regulator.

Upon receipt of a PPC from a client, the driver will validate that any
arguments supplied are valid before attempting an I²C transaction. If the
arguments supplied are not within the bounds of the regulator description
table, the driver returns an error to the client. Otherwise, it will
generate an I²C request to read or write appropriate state to the PMIC.


