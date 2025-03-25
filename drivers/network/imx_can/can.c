#include <stdint.h>
#include <microkit.h>
#include <sddf/resources/device.h>
#include <sddf/util/printf.h>

#include "can.h"

/*
    TODO
    > Atm none of the functions have any form of timeout or software error reporting - possibly should add this (similar to Linux kernel?)
    > Don't offer any configuration options - e.g. using the mailboxes and not FIFO, etc
*/

volatile struct control_registers *control_regs;
volatile struct error_registers *error_regs;
volatile struct canfd_registers *canfd_regs;

/* Specified in 11.8.2.11 - Reset */
static void soft_reset(void) {
    control_regs->mcr = MCR_SOFTRST;
    // Spin until SOFT_RESET is deasserted (this happens when the reset completes)
    while (control_regs->mcr & MCR_SOFTRST);
}

/* Specified in 11.8.2.1.1.1 */
static void freeze(void) {
    control_regs->mcr |= (MCR_HALT | MCR_FRZ);
    // Spin until FREEZE_ACK is asserted
    while (!(control_regs->mcr & MCR_FRZACK));
}

/* Specified in 11.8.2.1.1.1 */
static void unfreeze(void) {
    control_regs->mcr &= ~MCR_HALT;
    // Spin until FREEZE_ACK is deasserted
    while (control_regs->mcr & MCR_FRZACK); 
}

/* Specified in 11.8.4.1 - FlexCAN Initialization Sequence */
static void mcr_init(void) {
    /* TODO -- stuff the Linux kernel sets (or doesnt)
        - do I need to set max mailbox number here?
        - do I need to modify access (i.e. SUPV?)
        - do I need to set the ID acceptance mode? (IDAM)
        - do I need to set abort mechanism? Linux seems to ignore AEN
        - do I need the local priority bit? Linux also ignores this and it just adds backwards compatibility?
     */

    // Initial iteration only allows use of mailboxes and is fixed to normal mode

    // Enable individual Rx matching
    control_regs->mcr |= MCR_IRMQ;
    // Enable warning interrupts
    control_regs->mcr |= MCR_WRNEN;
    // Disable self-reception of frames (this needs to be enabled for loopback mode to work)
    control_regs->mcr |= MCR_SRXDIS;
    // Disable Rx FIFO (thus we're using mailboxes)
    control_regs->mcr &= ~MCR_RFEN;
    // Enable the abort mechanism for Tx MBs 
    control_regs->mcr |= MCR_AEN;
    // Enable the local priority bit for backwards compatibility
    control_regs->mcr |= MCR_LPRIOEN; 
}

/*
    // CBT - can bit timing register --> linux does this but can't find the implementation
    // CTRL1 - 

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
*/

#define MYBIT(x, y) (x << y)

// These are in order of hierarchy in the clock tree
volatile struct clock_registers *clock_reg_can_mux;
volatile struct clock_registers *clock_reg_ccgr53;
volatile struct clock_registers *pll1;
volatile struct clock_registers *clock_reg_ipg_root;

static void can_clocks_enable(void) {
    // TODO - need to map the clock registers to the system file so can access them

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
    // error_regs = (volatile struct error_registers *) (vaddr + ERROR_REGISTER_OFFSET);
    // canfd_regs = (volatile struct canfd_registers *) (vaddr + CANFD_REGISTER_OFFSET);
    
    // control_regs->mcr &= ~MCR_MDIS;

    sddf_dprintf("MCR register contains: %u\n", control_regs->mcr);


    // control_regs->mcr = (control_regs->mcr &= ~MCR_MDIS);
    // sddf_dprintf("The value of the mcr reg is %u\n", control_regs->mcr);
     // TODO - this bit enables/disables the module --> need to make sure its set first

    /* TODO - note that the Linux kernel does some extra setup here - ram_init and bittiming -- not certain if these are necessary or extra features? */

    /* Reset */
    // soft_reset();

    // /* Freeze */
    // freeze();

    // /* Module Configuration Register (MCR) init */
    // mcr_init();

    /*  */
}

// microkit init
void init (void) {
    sddf_printf("STARTING CAN DRIVER blah blah!\n");

    // Linux does the following before starting the initialisation process for flexcan
    // flexcan_transceiver_enable -- power regulator enable?
    // clocks enabled
    // • 0xA40 ~ 0xA7F: PGC for NOC mix
    // • 0xC00 ~ 0xC3F: PGC for MLMIX



    can_clocks_enable();

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