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
volatile struct acceptance_filter_registers *filter_regs;
volatile struct message_buffer *message_buffer;

// TODO - look into reading from mailbox via FlexCAN mailbox read - flexcan_mailbox_read -- STOPPED ON IMPLEMENTING THE BELOW

static void read_fifo(void) {
    // read the FIFO output

    // iflag1 contains the information about hte status of the FIFO buffers.
    // buf5I indicates whethere there is something in the FIFO to be read or not
    // buf6I indicates whether the FIFO is almost full
    // buf7I indicates a FIFO overflow has occurred

    /*
        -- TODO - look at flexcan memory buffer memory map pg5104 to determine where the buffers are -- the following section RX FIFO Structure is also
        worth looking at to understand this
        -- TODO - how do I determine the difference between a tx and rx buffer??? can any buffer be either???
        -- TODO - what is the expected size of the message buffer data region here??? We're not using canFD so it's presumably fixed to some size
        -- Assume atm the data segment is a fixed size of 8 bytes??? Does that mean the next MB is immediately afterwards or do we leave a large gap??
        in between????
        -- Looks like can_ctrl consists of 32 bits of data related to the buffer
        -- can_id is the identifier of the received message???
        Linux structure of the message buffer 
        // Structure of the message buffer
        struct flexcan_mb {
            u32 can_ctrl;
            u32 can_id;
            u32 data[];
        };
    */

   // Linux references to the message buffer area! If I can even read this that would be a start
   /*
    	struct_group(init,
		u8 mb[2][512];		// 0x80 - Not affected by Soft Reset
		// FIFO-mode:
		//  *			MB
		//  * 0x080...0x08f	0	RX message buffer
		//  * 0x090...0x0df	1-5	reserved
		//  * 0x0e0...0x0ff	6-7	8 entry ID table
		//  *				(mx25, mx28, mx35, mx53)
		//  * 0x0e0...0x2df	6-7..37	8..128 entry ID table
		//  *				size conf'ed via ctrl2::RFFN
		//  *				(mx6, vf610)
		 
   
   
   */
}

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

    // After this linux saves the state in the control register, then disables all those error masks we just enabled. We're ignoring this for the moment.
}


/* Specified in 11.8.2.14 -- Detection and correction of memory errors */
static void err_disable(void) {
    // Note: if we wanted to enable this we need to initialise the RAM. Linux initialises the ram in the call flexcan_ram_init

    // I think initially we'll disable the error correction functionality and we can know this exists for later. MECR[ECCDIS] controls this.
    // The protocol for disabling this is outlined in the above referenced section.
    // Note: if this doesn't seem to work Linux does one extra step for disabling some extra registers which might be necessary?
    control_regs->ctrl2 |= CTRL2_ECRWRE; // Enables updating of MECR
    error_regs->mecr &= ~MECR_ECRWRDIS; // Enables writing of MECR
    error_regs->mecr |= MECR_ECCDIS; // Disables memory and error correction functionality
    error_regs->mecr |= MECR_ECRWRDIS; // Disables writing to the MECR
    control_regs->ctrl2 &= ~CTRL2_ECRWRE; // Disable updating of MECR
}

static void message_buffer_init(void) {
    // Linux first clears and invalidates all the message buffers that aren't used -- This is on line 1595-1599. It leaves the initial 8 alone as I assume
    // these are used by the FIFO and then clears and invalidates the rest up to the maximum mailbox count.
    // TODO - Do I need to invalidat all the unused mailboxes?
    // TODO - Do I need to do any preparation for the mailboxes that are going to be used for RX FIFO?

    // Set all the masks to 'I don't care' so we accept everything
    control_regs->rxmgmask = 0x0;
    control_regs->rx14mask = 0x0;
    control_regs->rx15mask = 0x0;

    // Set all the Rx filters to 'I don't care' so we accept everything
    for (int i = 0; i < 16; i++ ) { // ATM We just fix this at 16 since we're using FIFO presumably we only use the lower 8 mailboxes so this shouldn't matter
        filter_regs->rxmir[i] = 0x0;
    }

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
#define CAN_CLOCK_MUX_REGISTER_OFFSET 0xa200
#define CAN_CLOCK_CCGR53_REGISTER_OFFSET 0x4350

static void can_clocks_enable(void) {
    uint64_t vaddr_ccm_base = 0x2000000; // TODO - #define this
    uint64_t vaddr_can_mux = vaddr_ccm_base + CAN_CLOCK_MUX_REGISTER_OFFSET;
    uint64_t vaddr_ccgr53 = vaddr_ccm_base + CAN_CLOCK_CCGR53_REGISTER_OFFSET;

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
    uint64_t vaddr = 0x1000000; // TODO - #define this
    control_regs = (volatile struct control_registers *) vaddr;
    filter_regs = (volatile struct acceptance_filter_registers *) (vaddr + ACCEPTANCE_FILTER_REGISTER_OFFSET);
    error_regs = (volatile struct error_registers *) (vaddr + ERROR_REGISTER_OFFSET);
    message_buffer = (volatile struct message_buffer *) (vaddr + FIFO_OUTPUT_BUFFER_OFFSET);

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

    // 0x800c0080 --> 0x800c0080  

    sddf_dprintf("The value in the ctrl1 register after initialisation is: %u\n", control_regs->ctrl1);
    sddf_dprintf("The value in the ctrl2 register after initialisation is: %u\n", control_regs->ctrl2);
    sddf_dprintf("The value in the error mecr register after initialisation is: %u\n", error_regs->mecr);
    sddf_dprintf("The value of the FIFO memory buffer ctrl is: %u\n", message_buffer->can_ctrl);
    sddf_dprintf("The value of the FIFO memory buffer ctrl is: %u\n", message_buffer->can_ctrl);
    sddf_dprintf("The value of the FIFO memory buffer id is: %u\n", message_buffer->can_id);
    sddf_dprintf("The value of the FIFO memory buffer data is: %u\n", message_buffer->data);
}

// microkit init
void init (void) {
    sddf_dprintf("STARTING CAN DRIVER\n");

    // Linux does the following before starting the initialisation process for flexcan
    // flexcan_transceiver_enable -- power regulator enable?

    // can_clocks_enable();

    can_init();

    // call all initialisation for the device / software interface here
    // first thing is basically going to be reading and writing a register
}

// microkit notified
void notified(microkit_channel ch) {
    // Whenever an interrupt is delivered we need to check here what kind of interrupt it was by looking at different registers
    // and then ACKING it using irq_ack once we work out what it is.
    sddf_dprintf("INTERRUPT RECEIEVED!");
}