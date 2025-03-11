#include <microkit.h>

#include "can.h"

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;

volatile struct control_registers *control_regs;
volatile struct error_registers *error_regs;
volatile struct canfd_registers *canfd_regs;

/* Specified in 11.8.2.11 - Reset */
static void soft_reset(void) {
    control_regs->mcr = MCR_SOFT_RESET;
    // Spin until SOFT_RESET is deasserted (this happens when the reset completes)
    while (control_regs->mcr & MCR_SOFT_RESET);
}

/* Specified in 11.8.2.1.1.1 */
static void freeze(void) {
    control_regs->mcr |= (MCR_HALT | MCR_FREEZE);
    // Spin until FREEZE_ACK is asserted
    while (!(control_registers->mcr & MCR_FREEZE_ACK));
}

/* Specified in 11.8.2.1.1.1 */
static void unfreeze(void) {
    control_regs->mcr &= ~MCR_HALT;
    // Spin until FREEZE_ACK is deasserted
    while (control_regs->mcr & MCR_FREEZE_ACK); 
}

/* Specified in 11.8.4.1 - FlexCAN Initialization Sequence */
static void can_setup(void) {
    /* Setup references to the different groups of registers */
    control_regs = device_resources.regions[0].region.vaddr;
    error_regs = device_resources.regions[0].region.vaddr + ERROR_REGISTER_OFFSET;
    canfd_regs = device_resources.regions[0].region.vaddr + CANFD_REGISTER_OFFSET;

    /* Reset */
    soft_reset();

    /* Freeze */
    freeze();

    /* MCR Register Setup */
    // TODO - stopped here -- following along the init process 
}

void init (void) {
    can_setup();
    // call all initialisation for the device / software interface here
    // first thing is basically going to be reading and writing a register
}

void notified(microkit_channel ch) {
    ;
}

/*
    TODO
    > Atm none of the functions have any form of timeout or software error reporting - possibly should add this (similar to Linux kernel?)
*/
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