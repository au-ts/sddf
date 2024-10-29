# Clock driver for iMX8M*

## Overview

This directory contains necessary files of implementing clock driver for
iMX8M* boards.

## Concepts

Internal Peripheral Gate (IPG) is a clock soure that provides the base 
timing signal for various internal peripherals within the SoC.

Low Power Clock Gating (LPCG) is used to manage on-chip peripheral clocks.
Clock root should stop if the LPCG is configured not to shutdown. 

## Usage

## Extention

## References

1. i.MX 8M Dual/8M QuadLite/8M Quad Applications Processors Reference Manual, Rev. 3.1, 06/2021.
