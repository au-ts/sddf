<!--
    Copyright 2026, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->
# sDDF ACPI Subsystem

On x86, Intel introduced the Advanced Configuration and Power Interface (ACPI)
to standardise the communication mechanism between the firmware and the host OS.
The firmware updates the platform configurations and power interface data in the
ACPI tables during the initialisation. This means the resources cannot be known
and allocated for the subsystems at build time like what is done on ARM and 
RISCV.

The Root System Description Pointer (RSDP) of these tables can either be 
obtained from the boot loader (in UEFI-based systems) or at fixed address (in 
legacy BIOS systems). In UEFI-based systems, the RSDP and other ACPI tables can
be anywhere in the memory, and can only be known at run time. 

## Dynamic ACPI tables mapping

So far, the seL4 kernel does not parse all the ACPI tables but passes RSDP as a
bootinfo block to the root task. The bootinfo pre-filling to user's memory was
partially supported by the rust capDL initialiser but not Microkit. This
[Microkit PR](https://github.com/seL4/microkit/pull/536) adds the support by
extending the pre-filling type of  `MemoryRegion`.

To self-map the ACPI tables, the ACPI driver needs to receive all the remaining
untypeds from the root task. The [draft 
implementation](https://github.com/seL4/rust-sel4/pull/322) is done by @syzmon, 
but it is a need to make an RFC to the capDL repository.

In this typical system, the untyped capabilities flow from the capDL initialiser
to the ACPI driver, and then some of them are handed off to the PCIe driver.
The existing `cap_sharing` feature in Microkit allows a PD to access to another
PD's CSpace, but it is obviously not safe to give the unrestricted access for a
specific use case. The solution here is to add a tag `cnode` that defines a
user-managed CNode and can be mapped to one or more PDs. There are already
[some discussions](https://github.com/seL4/microkit/pull/539) on this aggressive
change, and it still needs more input from the verification team.


## AML interpreter

The ACPI tables are compiled in ACPI Machine Language (AML) and stored as byte
code in memory, so another primary functionality of ACPI driver is parsing and
extracting required configuration information from the byte code. For the
verifiability and minimality of the ACPI driver,  the solution that might be
silly but necessary is to implement a simplified interpreter rather than to
integrate a third-party one.

The custom interpreter is implemented with a few simplified data structures:
- A finite state machine that manages the parsing state of current `operation`,
each `operation` having a known list of definition blocks.
- A state stack that saves the hierarchy of current parsing states.
- An object tree that connects all the parsed AML `operations`.

The ACPI driver firstly runs the interpreter on all the DSDT and SSDT tables
in `scan` mode and form a tree of AML objects. After finding the target object,
it runs the interpreter in `evaluation` mode to extract the data. The primary
reasons of doing this way are that there are some across-defined objects among
the tables, and the evaluation results depend on the `MethodOperation` execution
order and arguments.

## Dynamic resource mapping for subsystems

After the extraction, the ACPI driver places the subsystem-related resource
information in the shared memory and copies the corresponding capabilities to
the shared CNode, so the downstream subsystems can start its lifecylce with
everthing prepared. For now, we have only PCIe subsystem connected to the ACPI
driver. Other subsystems, such as timer, serial, power management, etc. should
be properly integrated on x86 as well.

## TODO List

- [ ] ACPI driver works as a [Post-initialiser](https://github.com/seL4/rfcs)
- [ ] Properly receive leftover untypeds from the capDL initialiser (RFC TBD)
- [ ] Passing IRQ routing tables to or set up IRQs for all the subsystems
- [ ] Self-map ACPI tables without untypeds for paging structures (by taking
advantages of driver image mapping)
