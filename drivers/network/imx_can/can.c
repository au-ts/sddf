#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>

#include "can.h"

/*
    TODO
    > Atm none of the functions have any form of timeout or software error reporting - possibly should add this (similar to Linux kernel?)
    > Don't offer any configuration options atm - e.g. using the mailboxes and not FIFO, etc
    > Make sure the regulator / transceiver is turned on or we won't be able to communicate with the bus

*/

volatile struct control_registers *control_regs;
volatile struct error_registers *error_regs;
volatile struct canfd_registers *canfd_regs;

/* Copied from flexcan-core.c in Linux kernel */
static void module_enable(void) {
    control_regs->mcr &= ~MCR_MDIS;
    // Spins until the Low Power Mode Acknowledge is deasserted (when low power mode is exited)
    while (control_regs->mcr & MCR_LPMACK);
}

/* Specified in 11.8.2.11 - Reset */
static void soft_reset(void) {
    control_regs->mcr = MCR_SOFTRST;
    // Spin until Soft Reset is deasserted (this happens when the reset completes)
    while (control_regs->mcr & MCR_SOFTRST);
}

/* Specified in 11.8.2.1.1.1 */
static void freeze(void) {
    control_regs->mcr |= (MCR_HALT | MCR_FRZ);
    // Spin until Freeze Acknowledge is asserted
    while (!(control_regs->mcr & MCR_FRZACK));
}

/* Specified in 11.8.2.1.1.1 */
static void unfreeze(void) {
    control_regs->mcr &= ~MCR_HALT;
    // Spin until Freeze Acknowledge is deasserted
    while (control_regs->mcr & MCR_FRZACK); 
}

/* Specified in 11.8.4.1 - FlexCAN Initialization Sequence */
static void mcr_init(void) {
    // Set to value of last message buffer to be used in filter and arbitration process
    control_regs->mcr &= ~MCR_MAXMB(0x7f); // First we clear it
    control_regs->mcr |= MCR_MAXMB(0x7f); // Then we set it TODO: what should this value be if we want to use the FIFO? It says we need to consider that when setting this.
    // Allow supervisor access so we can access the other registers when not in supervisor mode (i.e. userspace)
    control_regs->mcr &= ~MCR_SUPV;
    // Enables TWRNINT and RWRNINT flags in ESR1 to be raised. Else they're always 0.
    control_regs->mcr |= MCR_WRNEN;
    // Enables individual Rx masking and queue features 
    control_regs->mcr |= MCR_IRMQ; // TODO: Not certain whether I want this on or not for FIFO just yet. Look into it further.
    // Disable self-reception of frames (this needs to be enabled for loopback mode to work)
    control_regs->mcr |= MCR_SRXDIS;
    // Enable Rx FIFO
    control_regs->mcr |= MCR_RFEN;
    // Set the Rx FIFO filter table format
    control_regs->mcr |= MCR_IDAM(0x2); // TODO: ATM just set this to format C but need to understand what the correct option is here 
    // Enable the abort mechanism for Tx MBs 
    control_regs->mcr |= MCR_AEN; // TODO: not sure why but linux doesn't enable this. Might be default enabled?
    // Enable the local priority bit for backwards compatibility
    control_regs->mcr |= MCR_LPRIOEN; // TODO: not sure this should be enabled - try disabling if run into issues.
    // Disable CANFD
    control_regs->mcr &= ~MCR_FDEN;
}

/* Specified in 11.8.4.1 - FlexCAN Initialization Sequence */
static void ctrl_init(void) {
    // Note: we assume here we're not setting up CANFD so we ignore any config for it atm

    // Disable loopback mode, listen-only mode and choose to use only a single sample for sampling mode
    control_regs->ctrl1 &= ~(CTRL1_LPB | CTRL1_LOM | CTRL1_SMP);

    // Reset bit timing parameters and bit rate
    control_regs->ctrl1 &= ~(CTRL1_PRESDIV(255UL) | CTRL1_RJW(3UL) | CTRL1_PSEG1(7UL) | CTRL1_PSEG2(7UL) | CTRL1_PROPSEG(7UL));
    
    // TODO - Currently not sure what these should be. Linux reads them from the device configuration so here we just use 
    // some dummy values for the moment -- doc here can help calculate and there also seems to be online calculators for this
    // https://community.nxp.com/pwmxy87654/attachments/pwmxy87654/mpc5xxx%40tkb/292/1/FlexCAN%20bit%20timing.pdf
    
    // Set bit timing parameters and bit rate --  Note these are dummy values. Could look at flexcan_bittiming_const from flexcan_core.c
    control_regs->ctrl1 |= (CTRL1_PRESDIV(255UL) | CTRL1_RJW(3UL) | CTRL1_PSEG1(7UL) | CTRL1_PSEG2(7UL) | CTRL1_PROPSEG(7UL));

    // Some extra ctrl configuration Linux does for FlexCAN
    // Disable the timer sync feature
    control_regs->ctrl1 &= ~CTRL1_TSYN;
    // Disable auto busoff recovery and choose the lowest buffer first in Tx
    control_regs->ctrl1 |= (CTRL1_BOFFREC | CTRL1_LBUF);
    // Enable error masks for TWRNINT, RWRNINT and BOFFINT in ESR1
    control_regs->ctrl1 |= (CTRL1_TWRNMSK | CTRL1_RWRNMSK | CTRL1_BOFFMSK);
    // Enable error mask for ERRINT in ESR1 as well (this seems to be depend on the flexcan core but we assume for the moment we'll need it)
    control_regs->ctrl1 |= CTRL1_ERRMSK;

    // After this linux saves the state in the control register, then disables all those error masks we just enabled
    // I think I can then jump to line 1595 where we clear and invalidate unused mailboxes. The initialisation guide could be hten step 3 or 4. STOPPED HERE
}

#define CTRL2_ECRWRE    (1UL << 29) // Error correction configuration register write enable. Enables MECR to be updated 0 = disable update, 1 = enable update
#define MECR_ECRWRDIS   (1UL << 31) // Error configuration register write disable. Disables write on this register 0 = write is enabled, 1 = write is disabled
#define MECR_ECCDIS     (1UL << 8)  // Error correction disable. Disables memory detection and correction mechanism. 0 = enable correction, 1 = disable correction

/* Specified in 11.8.2.14 -- Detection and correction of memory errors */
static void err_disable(void) {
    // TODO -- up to 1538 >> Err handling enabled??? Need to initialize all the ram for this?
    // Linux initialises the ram in the call flexcan_ram_init

    // I think initially we'll disable the error correction functionality and we can know this exists for later. MECR[ECCDIS] controls this.
    // The protocol for disabling this is outlined in the above referenced section.
    control_regs->ctrl2 |= CTRL2_ECRWRE; // Enables updating of MECR
    error_regs->mecr &= ~MECR_ECRWRDIS; // Enables writing of MECR
    error_regs->mecr |= MECR_ECCDIS; // Disables memory and error correction functionality
    error_regs->mecr |= MECR_ECRWRDIS; // Disables writing to the MECR
}

static void message_buffer_init(void) {
    /*
        4. Initialize the message buffers.
            a. The control and status word of all message buffers must be initialized.
            b. If Rx FIFO was enabled, the ID filter table must be initialized.
            c. Other entries in each message buffer should be initialized as required.
    */
}

#define MYBIT(x, y) (x << y)

// These are in order of hierarchy in the clock tree
volatile struct clock_registers *clock_reg_can_mux;
volatile struct clock_registers *clock_reg_ccgr53;
volatile struct clock_registers *pll1;
volatile struct clock_registers *clock_reg_ipg_root;

static void can_clocks_enable(void) {
    uint64_t vaddr_ccm_base = 0x2000000;
    uint64_t vaddr_can_mux = vaddr_ccm_base + 0xa200; // TODO - define for offsets
    uint64_t vaddr_ccgr53 = vaddr_ccm_base + 0x4350; // TODO - define for offsets

    // FlexCAN requires pll1 -- seems like from clock dump that it's available
    // disable flexcan clock root
    // set flexcan clock root to system pll1 divided by 5
    // enable flexcan clock root

    uint64_t vaddr_ipg_root = vaddr_ccm_base + 0x9000; 
    clock_reg_ipg_root = (volatile struct clock_registers *) vaddr_ipg_root;
    
    pll1 = (volatile struct clock_registers *) (vaddr_ccm_base + 0x0940);
    clock_reg_can_mux = (volatile struct clock_registers *) vaddr_can_mux;
    clock_reg_ccgr53 = (volatile struct clock_registers *) vaddr_ccgr53;

    pll1->set = MYBIT(0x3, 0);
    pll1->base = MYBIT(0x3, 0);
    
    // Disable the ccgr
    clock_reg_ccgr53->clr = MYBIT(0x3, 0);

    // Set the mux to select the 3rd parent
    clock_reg_can_mux->base = MYBIT(0x3, 24);

    // Enable the clock
    clock_reg_can_mux->set = (MYBIT(0x1, 28) | MYBIT(0x2, 0));

    clock_reg_ccgr53->set |= MYBIT(0x3, 0);

    clock_reg_ipg_root->set = MYBIT(0x3, 0);
    clock_reg_ipg_root->base = MYBIT(0x1, 28);

    // print base and set of registers
    sddf_dprintf("pll1 >> Base: %x , Set: %x\n", pll1->base, pll1->set);
    sddf_dprintf("CCGR >> Base: %x , Set: %x\n", clock_reg_ccgr53->base, clock_reg_ccgr53->set);
    sddf_dprintf("MUX >> Base: %x , Set: %x\n", clock_reg_can_mux->base, clock_reg_can_mux->set);
    sddf_dprintf("IPG >> Base: %x , Set: %x\n", clock_reg_ipg_root->base, clock_reg_ipg_root->set);
}

/* Specified in 11.8.4.1 - FlexCAN Initialization Sequence */
static void can_init(void) {
    /* Setup references to the different groups of registers */
    uint64_t vaddr = 0x1000000;
    control_regs = (volatile struct control_registers *) vaddr;
    error_regs = (volatile struct error_registers *) (vaddr + ERROR_REGISTER_OFFSET);
    // canfd_regs = (volatile struct canfd_registers *) (vaddr + CANFD_REGISTER_OFFSET);

    sddf_dprintf("The value in the ctrl1 register is: %u\n", control_regs->ctrl1);
    sddf_dprintf("The value in the ctrl2 register is: %u\n", control_regs->ctrl2);
    sddf_dprintf("The value in the error mecr register is: %u\n", error_regs->mecr);
    
    // /* Enable the module */
    // module_enable();

    // /* Soft reset */
    // soft_reset();

    // TODO - Linux's implementation calls additional functions here
    // First it calls flexcan_ram_init here to allow write access to certain addresses - not sure if I need this
    // Second it calls flexcan_set_bittiming which sets up some information in the control register -- atm I've delayed bitttiming to within ctrl_init
    // which is where the manual discusses the initialisation

    // /* Freeze */
    // freeze();

    // /* Module Configuration Register (MCR) init */
    // mcr_init();

    /* Control1 Register (ctrl1) Init */
    ctrl_init();

    /* Disable error correction */
    // Note: We might enable this later but atm we're trying with this disabled for simplicity
    err_disable();

    sddf_dprintf("The value in the ctrl1 register after initialisation is: %u\n", control_regs->ctrl1);
    sddf_dprintf("The value in the ctrl2 register after initialisation is: %u\n", control_regs->ctrl2);
    sddf_dprintf("The value in the error mecr register after initialisation is: %u\n", error_regs->mecr);
}

// microkit init
void init (void) {
    sddf_printf("STARTING CAN DRIVER blah blah!\n");

    // Linux does the following before starting the initialisation process for flexcan
    // flexcan_transceiver_enable -- power regulator enable?

    // can_clocks_enable();

    can_init();

    // call all initialisation for the device / software interface here
    // first thing is basically going to be reading and writing a register
}

// microkit notified
void notified(microkit_channel ch) {
    ;
}

// Initially just boot the device and try to read and write one of the registers in the Module Configuration Register (MCR)

// Implementation for initialisation
// Reset --> I think it's safe to assume booting is chip-level reset so we don't need to reset again on startup
// Freeze --> before any initialisation can begin, need to set freeze mode
// Init process

// << INIT PROCESS >> 
/*
    For any configuration change/initialization it is required that FlexCAN be put into Freeze
    mode (see Freeze mode). Note that the module needs to be initialized after every reset.
    The following is a generic initialization sequence applicable to the FlexCAN module:
    1. Initialize the Module Configuration register (MCR).
    a. Enable the individual filtering per MB and reception queue features by setting
    IRMQ.
    b. Enable the warning interrupts by setting WRNEN.
    c. If required, disable frame self reception by setting SRXDIS.
    d. Enable the Rx FIFO by setting RFEN.
    e. If Rx FIFO is enabled and DMA is required, set DMA.
    f. Enable the abort mechanism by setting AEN.
    g. Enable the local priority feature by setting LPRIOEN.
    2. Initialize the Control 1 register (CTRL1) and optionally the CAN Bit Timing register
    (CBT). Initialize also the CAN FD CAN Bit Timing register (FDCBT).
    a. Determine the bit timing parameters: PROPSEG, PSEG1, PSEG2, and RJW.
    b. Optionally determine the bit timing parameters: EPROPSEG, EPSEG1,
    EPSEG2, and ERJW.
    c. Determine the CAN FD bit timing parameters: FPROPSEG, FPSEG1, FPSEG2,
    and FRJW.
    d. Determine the bit rate by programming the PRESDIV field and optionally the
    EPRESDIV field.
    e. Determine the CAN FD bit rate by programming the FPRESDIV field.
    f. Determine the internal arbitration mode (LBUF).
    3. All FlexCAN memory must be initialized if Error Code Correction (ECC) is enabled.
    See Detection and correction of memory errors.
    4. Initialize the message buffers.
    a. The control and status word of all message buffers must be initialized.
    b. If Rx FIFO was enabled, the ID filter table must be initialized.
    c. Other entries in each message buffer should be initialized as required.
    5. Initialize the Rx Individual Mask registers (RXIMRn).
    6. Set required interrupt mask bits in
    • IMASK registers (for all MB interrupts)
    • MCR register (for Wake-Up interrupt)
    • CTRL1 / CTRL2 registers (for Bus Off and Error interrupts)
    7. Negate MCR[HALT].
    After the last step listed above, FlexCAN attempts to synchronize to the CAN bus.
*/