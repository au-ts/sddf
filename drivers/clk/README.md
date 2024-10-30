# Clock Driver

## Overview

Each SoC has a tree of gates, multiplexers, dividers, and phase-locked-loops
(PLL) that take external clock inputs (e.g., from a crystal), and derive
other frequencies from them. A clock driver in an SoC environment is a kernel
component that manages the clock infrastructure for hardware devices in the
system. The clock driver is responsible for providing, controlling, and
configuring clock signals for various peripherals, CPUs, and subsystems. 

The common clock framework (CCF) in Linux was introduced ot address the
growing complexity of clock management in modern SoCs. It abstracts the
features of clock hardware and provides a set of unified interfaces
to allows device drivers to interact with clocks. Clock providers are
hardware blocks that generate and control clocks, such as oscillators,
PLLs, and dividers. Clock consumers are devices or peripherals that require
clock signals to function and can interact with the clock framework via
the exposed interfaces.

We adhere to the CCF and allows the consumers to request and control via a
unified API, which is essentially a remote-procedure call.

Before the clock driver is built, a Python script parses the device tree and
generates a C header file that specifies required clocks and corresponding
rates at compile time. The clock driver must be given a highest priority to
ensure that it is initialised earlier than all potential users in the system.
At `init()` time, the driver initialises the clock tree based on the generated
`clk_conf.h` file which can also be manually modified to specify a clock
frequency.

The below picture gives a sample of how a clock tree looks like:

![Figure 1. Sample diagram of clock tree](./sub_clock_tree.png)

## Usage

This driver can be used as a clock server to manage and control clock hardware in
a SoC. To initialise the whole clock tree, a DTS file is required to be prepared.

To control the clocks, the following APIs can be invoked at userspace:
- `static inline uint32_t sddf_clk_enable(microkit_channel channel, uint32_t clk_id)`
- `static inline uint32_t sddf_clk_disable(microkit_channel channel, uint32_t clk_id)`
- `static inline uint32_t sddf_clk_get_rate(microkit_channel channel, uint32_t clk_id)`
- `static inline uint32_t sddf_clk_set_rate(microkit_channel channel, uint32_t clk_id, uint32_t rate)`

`clk_id` can be found in the corresponding binding file:
- Odroid-C4: `sddf/drivers/clk/meson/include/g12a-clkc.h`
- iMX8MQ: `sddf/drivers/clk/imx/include/imx8mq.h`

See `include/sddf/clk/client.h` for more details.

## Odroid C4

@terryb FILL IN

## iMX8-*

**VMM Changes**
> The VMM library then calls into the Pinmux or Clock drivers to see if what has been requested is compatible with what actually has been set.

We check if the requested values are compatible with what actually has been set in VMM. For clock requests, the VMM hands over the faulting information to the handler in clock driver via RPC.

In GPU driver in Linux codebase, there are some non-standard clock configurations (writing registers without requesting clock driver) implemented by the SoC manufactorer, so we define a set of registers that Framebuffer Driver VM allows to write to. This will be fixed by intercepting the clock requests and dynamically adjusting clocks for the consumers.

**Next Steps**
> The system we’ve designed is intended to set all pinmux and clocks at boot time, and never allow them to be changed at runtime. This is adequate for many devices.






## Notes

HHI_SYS_PLL_CNTL0 - 0xff63c2f4
- sys_pll_dco
- sys_pll

HI_MALI_CLK_CNTL - 0x0xff63c1b0
- g12a_mali_0_sel
- g12a_mali_0_div
- g12a_mali_0
- g12a_mali_1_sel
- g12a_mali_1_div
- g12a_mali_1
- g12a_mali

HHI_HDMI_PHY_CNTL0 - 0xff63c3a0
- 

HHI_SYS_CPU_CLK_CNTL0 - 0xff63c19c
- g12a_cpu_clk
- g12a_cpu_clk_dyn
- g12a_cpu_postmux0
- g12a_cpu_postmux1
- g12a_cpu_mux0_div
- g12a_cpu_mux1_div
- g12a_cpu_premux0
- g12a_cpu_premux1

HHI_HDMI_PLL_CNTL0 - 0xff63c320
- 

CLK DRIVER|INFO: write 0x100 to 0xff63c1b0
CLK DRIVER|INFO: write 0xa4020000 to 0xff63c19c
CLK DRIVER|INFO: write 0xf80204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x280204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x2802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0xd801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x4020800 to 0xff63c19c
CLK DRIVER|INFO: write 0x0 to 0xff63c3a0

CLK DRIVER|INFO: write 0xa4020000 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x28010496 to 0xff63c2f4
CLK DRIVER|INFO: write 0x38010496 to 0xff63c2f4
CLK DRIVER|INFO: write 0x18010496 to 0xff63c2f4
CLK DRIVER|INFO: write 0x4020800 to 0xff63c19c

CLK DRIVER|INFO: write 0xa4000800 to 0xff63c19c
CLK DRIVER|INFO: write 0xa4000c00 to 0xff63c19c
CLK DRIVER|INFO: write 0xc4000c01 to 0xff63c19c
CLK DRIVER|INFO: write 0xc4000801 to 0xff63c19c
CLK DRIVER|INFO: write 0xa4000001 to 0xff63c19c
CLK DRIVER|INFO: write 0x1 to 0xff63c19c

CLK DRIVER|INFO: write 0xf8010496 to 0xff63c2f4
CLK DRIVER|INFO: write 0x28010496 to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c

CLK DRIVER|INFO: write 0xb3a047b to 0xff63c320
CLK DRIVER|INFO: write 0xbb3a047b to 0xff63c320
CLK DRIVER|INFO: write 0x18000 to 0xff63c324
CLK DRIVER|INFO: write 0xa691c00 to 0xff63c32c
CLK DRIVER|INFO: write 0x33771290 to 0xff63c330
CLK DRIVER|INFO: write 0x39270000 to 0xff63c334
CLK DRIVER|INFO: write 0x50540000 to 0xff63c338
CLK DRIVER|INFO: write 0x1b3a047b to 0xff63c320
CLK DRIVER|INFO: write 0xdb38047b to 0xff63c320
CLK DRIVER|INFO: write 0xdb34047b to 0xff63c320
CLK DRIVER|INFO: write 0xdb14047b to 0xff63c320
CLK DRIVER|INFO: write 0x2739c to 0xff63c1a0
CLK DRIVER|INFO: write 0x739c to 0xff63c1a0
CLK DRIVER|INFO: write 0x0 to 0xff63c1a0
CLK DRIVER|INFO: write 0x20000 to 0xff63c1a0
CLK DRIVER|INFO: write 0x28000 to 0xff63c1a0
CLK DRIVER|INFO: write 0x2f39c to 0xff63c1a0
CLK DRIVER|INFO: write 0x2739c to 0xff63c1a0
CLK DRIVER|INFO: write 0xa739c to 0xff63c1a0
CLK DRIVER|INFO: write 0x33eb4242 to 0xff63c3a0
CLK DRIVER|INFO: write 0x3900000 to 0xff63c3a4
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x280104ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x380104ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x180104ea to 0xff63c2f4
CLK DRIVER|INFO: write 0xd80204ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf80204ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x280204ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x2802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0xd801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x3801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x1801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x280104fa to 0xff63c2f4
CLK DRIVER|INFO: write 0x380104fa to 0xff63c2f4
CLK DRIVER|INFO: write 0x180104fa to 0xff63c2f4
CLK DRIVER|INFO: write 0xd80204fa to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf80204fa to 0xff63c2f4
CLK DRIVER|INFO: write 0x280204fa to 0xff63c2f4
CLK DRIVER|INFO: write 0x2802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0xd801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c

CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x280104c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x380104c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x180104c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0xd80204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf80204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x280204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x2802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0xd801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x3801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x1801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801048e to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c

CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x33eb4242 to 0xff63c3a0
CLK DRIVER|INFO: write 0x3900000 to 0xff63c3a4

CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x280104c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x380104c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x180104c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0xd80204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf80204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x280204c8 to 0xff63c2f4
CLK DRIVER|INFO: write 0x2802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0xd801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4

CLK DRIVER|INFO: write 0x0 to 0xff63c3a0
CLK DRIVER|INFO: write 0xb3a04aa to 0xff63c320
CLK DRIVER|INFO: write 0xbb3a04aa to 0xff63c320
CLK DRIVER|INFO: write 0x5555 to 0xff63c324
CLK DRIVER|INFO: write 0x1b3a04aa to 0xff63c320
CLK DRIVER|INFO: write 0xdb3604aa to 0xff63c320
CLK DRIVER|INFO: write 0xdb0604aa to 0xff63c320
CLK DRIVER|INFO: write 0x2739c to 0xff63c1a0
CLK DRIVER|INFO: write 0x739c to 0xff63c1a0
CLK DRIVER|INFO: write 0x0 to 0xff63c1a0
CLK DRIVER|INFO: write 0x20000 to 0xff63c1a0
CLK DRIVER|INFO: write 0x28000 to 0xff63c1a0
CLK DRIVER|INFO: write 0x2f39c to 0xff63c1a0
CLK DRIVER|INFO: write 0x2739c to 0xff63c1a0
CLK DRIVER|INFO: write 0xa739c to 0xff63c1a0


CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x2801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x280104ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x380104ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x180104ea to 0xff63c2f4
CLK DRIVER|INFO: write 0xd80204ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c
CLK DRIVER|INFO: write 0xf80204ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x280204ea to 0xff63c2f4
CLK DRIVER|INFO: write 0x2802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x3802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x1802049f to 0xff63c2f4
CLK DRIVER|INFO: write 0xd801049f to 0xff63c2f4
CLK DRIVER|INFO: write 0x801 to 0xff63c19c
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000f to 0xff63c3a4
CLK DRIVER|INFO: write 0x390000e to 0xff63c3a4

CLK DRIVER|INFO: write 0x80000001 to 0xff63c19c