<!--
    Copyright 2025, UNSW

    SPDX-License-Identifier: BSD-2-Clause
-->

# Available drivers

Below is a list of all the avaiable drivers in sDDF, grouped by
their device class.

Each driver is listed by the device family it is written for
and a list of Device Tree compatible strings it is known to work with.

## Block

* i.MX8 uSDHC
    * `fsl,imx8mq-usdhc`
* virtIO block
    * `virtio,mmio`

## I<sup>2</sup>C

* Meson
    * `amlogic,meson-axg-i2c`

## Network

* DWMAC
    * `nxp,imx8mp-dwmac-eqos`
    * `snps,dwmac-5.10a`
    * `snps,dwmac-5.20`
    * `eswin,eic7700-qos-eth`
* i.MX8
    * `fsl,imx8mq-fec`
* Meson
    * `amlogic,meson-gxbb-dwmac`
    * `amlogic,meson-g12a-dwmac`
* virtIO network
    * `virtio,mmio`

## GPU

* virtIO GPU (2D only)
    * `virtio,mmio`

## Serial

* ARM UART
    * `arm,pl011`
* i.MX8 UART
    * `fsl,imx8mq-uart`
    * `fsl,imx8mm-uart`
    * `fsl,imx8mp-uart`
* NS16550A
    * `brcm,bcm2835-aux-uart`
    * `starfive,jh7110-uart`
    * `ns16550a`
* AMD Zynq UltraScale+ MPSoC UART
    * `xlnx,zynqmp-uart`
* virtIO console
    * `virtio,mmio`

## Timer

* ARM architectural timer
    * `arm,armv8-timer`
* Google Goldfish RTC
    * `google,goldfish-rtc`
* i.MX8 General Purpose Timer
    * `fsl,imx8mm-gpt`
    * `fsl,imx8mq-gpt`
    * `fsl,imx8mp-gpt`
* Meson
    * `amlogic,meson-gxbb-wdt`
* StarFive JH7110
    * `starfive,jh7110-timer`
* Cadence
    * `cdns,ttc`
* BCM2835
    * `brcm,bcm2835-system-timer`
