# Freescale i.MX PWM controller

Implementation of `linux/Documentation/devicetree/bindings/pwm/pwm-imx.yaml` driver.

Specifically the 'fsl,imx8mq-pwm' driver implemented on the MaaXboard.


MaaXboard has under `iomuxc@30330000`:

```
pwm2_grp {
    fsl,pins = <0x5c 0x2c4 0x00 0x05 0x00 0x06>;
    phandle = <0x1f>;
};

pwm4_grp {
    fsl,pins = <0x64 0x2cc 0x00 0x05 0x00 0x06>;
    phandle = <0x20>;
    };
```


chapter 8 chip io and pinmux

PWM
    PWM2_OUT    I2C4_SCL (ALT1) / SPDIF_RX (ALT1) / GPIO1_IO13 (ALT5)
    PWM4_OUT    I2C3_SCL (ALT1) / SAI3_MCLK (ALT1) / GPIO1_IO15 (ALT5)

using pwm2

```

            pwm2: pwm@30670000 {
                compatible = "fsl,imx8mq-pwm", "fsl,imx27-pwm";
                reg = <0x30670000 0x10000>;
                interrupts = <GIC_SPI 82 IRQ_TYPE_LEVEL_HIGH>;
                clocks = <&clk IMX8MQ_CLK_PWM2_ROOT>,
                         <&clk IMX8MQ_CLK_PWM2_ROOT>;
                clock-names = "ipg", "per";
                #pwm-cells = <3>;
                status = "disabled";
            };
```
