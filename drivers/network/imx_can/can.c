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
    > Do we need to turn on the clocks or are they already on?
*/

volatile struct control_registers *control_regs;
volatile struct error_registers *error_regs;
volatile struct canfd_registers *canfd_regs;
volatile struct acceptance_filter_registers *filter_regs;
// volatile struct message_buffer *fifo_output_buffer;

/* Specified in 11.8.2.8 - Rx FIFO */
// static uint64_t read_fifo(void) {
//     // Read the contents of RXFIR
//     // TODO - at the moment we're trying to accept all messages so we ignore this. Need to update to report ID of found message.

//     // Read the message
//     uint64_t message = fifo_output_buffer->data;

//     // Check for overflow occurred
//     if (control_regs->iflag1 & IFLAG1_BUF7I) {
//         sddf_dprintf("Rx FIFO has overflowed!\n");
//     }

//     // Check for warning FIFO almost full
//     if (control_regs->iflag1 & IFLAG1_BUF6I) {
//         sddf_dprintf("Rx FIFO almost full!\n");
//     }

//     // Clear the frame is available buffer (and other flags) - note that this will retrigger an interrupt if there's more unserviced buffers in the FIFO
//     control_regs->iflag1 &= ~(IFLAG1_BUF7I | IFLAG1_BUF6I | IFLAG1_BUF5I);

//     return message;
// }


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

/* Message Buffer Structure - 11.8.5.3  */
// Control bits
#define MB_CTRL_EDL             (1UL << 31)             /* Extended Data Length -- Distinguishes between CAN and CANFD frames */
#define MB_CTRL_BRS             (1UL << 30)             /* Bit Rate Switch -- Defines whether bit rate switch is in CANFD frame */
#define MB_CTRL_ESI             (1UL << 29)             /* Error State Indicator -- Indicates if transmitting node is error active or error passive */
#define MB_CTRL_RESERVED0       (1UL << 28)             /* Reserved */
#define MB_CTRL_CODE(x)         (((x) & 15UL) << 24)    /* Message Buffer Code -- See below for details*/
#define MB_CTRL_RESERVED1       (1UL << 23)             /* Reserved */
#define MB_CTRL_SRR             (1UL << 22)             /* Substitute Remote Request -- Used only in extended format*/
#define MB_CTRL_IDE             (1UL << 21)             /* ID Extended Bit -- Identifies whether frame is standard or extended */
#define MB_CTRL_RTR             (1UL << 20)             /* Remote Transmission Request -- Used for arbitration (see Table 11-186 for details)*/
#define MB_CTRL_DLC(x)          (((x) & 15UL) << 16)    /* Length of Data Bytes -- Contains the length in bytes of the Rx or Tx data */
#define MB_CTRL_TIMESTAMP       (65535UL << 0)          /* Free-Running Counter Time Stamp -- Copy of the free-running timer value at Rx or Tx time */
// Id bits      
#define MB_ID_PRIO              (7UL << 29)             /* Local Priority -- Only used for Tx */
#define MB_ID_STD               (2047UL << 18)          /* Frame Identifier -- In standard only the 11 most significant bits are used */
#define MB_ID_EXT               (262143UL << 0)         /* Extended Identifier -- If extended is used both the 11 top and 18 bottom bits used for identifier */

/*
    Message Buffer Codes (Rx) -- See Table 11-186 for further details
    > 0000b: MB is inactive
    > 0100b: MB is active and empty
    > 0010b: MB is full
    > 0110b: MB is full and contains an overrun (written over a previous buffer)
    > 1010b: A frame configured to recognize remote request frame
    > If Code[0] == 1, FlexCAN is updating the contents of the MB and the CPU must not access it
*/

#define CODE_RX_INACTIVE    0x0 /* Won't store any data or do anything */
#define CODE_RX_EMPTY       0x4 /* Ready to receive data from a frame */
#define CODE_RX_FULL        0x2 /* Contains data from a frame */
#define CODE_TX_INACTIVE    0x8 /* Emtpy and can be setup to transmit */
#define CODE_TX_DATA        0xc /* Data ready for transmit --> goes to inactive after transmit */

/* Message Buffer Setup */
#define MESSAGE_BUFFERS_START 0x80
struct message_buffer { // We have 16 byte message buffers holding 8 byes of metadata and 8 of data
    uint32_t can_ctrl;
    uint32_t can_id;
    uint64_t data; // Note: this is fixed at 8 bytes as we're currently using standard CAN and not CANFD
};

struct message_buffer_container { // we have 64 message buffers
    struct message_buffer mb[64]; // TODO: This is a bit of hard coding where we assume max 8 byte payloads - should update
};

volatile struct message_buffer_container *message_buffers;


/* Specified in 11.8.4.1 - FlexCAN Initialization Sequence */
static void can_init(void) {
    /* Setup references to the different groups of registers */
    uint64_t vaddr = 0x1000000; // TODO - #define this
    control_regs = (volatile struct control_registers *) vaddr;
    filter_regs = (volatile struct acceptance_filter_registers *) (vaddr + ACCEPTANCE_FILTER_REGISTER_OFFSET);
    error_regs = (volatile struct error_registers *) (vaddr + ERROR_REGISTER_OFFSET);
    message_buffers = (volatile struct message_buffer_container *) (vaddr + MESSAGE_BUFFERS_START);

    // NOTE: Most of the initialisation for this is handled in the loader atm. This currently just
    // sets up the memory regions for different registers. The source of truth for initialisation is now
    // the hack setup in the microkit loader.

    /* Configuration for the message buffers */
    // We make some assumptions here:
    // 1. We're not using the FIFO
    // 2. We're not using CANFD
    // 3. Only one message buffer is used for Tx (MB0)
    // 4. We're using all 64 mailboxes and each contains up to 8 bytes of data (and 8 bytes for id/ctrl)

    message_buffers->mb[0].can_ctrl |= MB_CTRL_CODE(CODE_TX_INACTIVE); // Set the first MB as Tx

    for (int i = 1; i < 64; i++) { // Set the remaining MBs as Rx
        message_buffers->mb[i].can_ctrl |= MB_CTRL_CODE(CODE_RX_EMPTY);
    }
}

/*
    8. Configure the Control and Status word with the desired configuration.
        a. Set ID type via MB_CS[IDE].
        b. Set Remote Transmission Request (if needed) via MB_CS[RTR].
        c. If MCR[FDEN] is enabled, also configure the MB_CS[EDL] and MB_CS[BRS]
        fields. For details about the relationship between the written value and
        transmitted value of the MB_CS[ESI] field, see Table 11-165.2
        d. Set Data Length Code in bytes via MB_CS[DLC]. See Table 11-188 for detailed
        information.
        e. Activate the message buffer to transmit the CAN frame by setting
        MB_CS[CODE] to Ch.

*/

/* Specified in 11.8.2.2 - Transmit Process */
static void can_tx(void) { // TODO - add parameters

    // TODO - we should probably do some clearing up here to make sure the interrupt bits aren't set

    uint32_t id = (123UL << 18); // A standad can frame (without extended ID only uses the middle 11 bits)

    uint64_t data = 0xffffffffffffffff; // Some dummy data

    uint32_t ctrl = MB_CTRL_CODE(CODE_TX_DATA); // Set the data code to indicate we have a message to send
    ctrl |= MB_CTRL_DLC(8); // Indicate we're sending an 8 byte data segment
    ctrl &= ~(MB_CTRL_IDE | MB_CTRL_BRS | MB_CTRL_ESI | MB_CTRL_EDL | MB_CTRL_RTR); // We don't want any of this (not sure about ESI though)

    message_buffers->mb[0].can_id = id;
    message_buffers->mb[0].data = data;    
    message_buffers->mb[0].can_ctrl |= ctrl; // Write the whole control word in a single write -- this triggers the transmission
}

/* Specified in 11.8.2.4 - Receive Process */
static void can_rx(int index) {
    sddf_dprintf("TODO: implement reading MB contents, atm we just print the MB number we'd like to read: %d\n", index);
    // Linux handles this in flexcan_mailbox_read 
}


static void handle_irq(microkit_channel ch) {

    /*
        3 primary types of interrupts:
         - Reception of frame
         - Transmission complete
         - Error/status changes
    */
    
    // Reception interrupts
    for (int i = 1; i < 32; i++) { // iflag1 (mb1 -31)
        if (MYBIT(1, i) & control_regs->iflag1) { // Check for the corresponding flag
            can_rx(i); // read the corresponding message buffer
            control_regs->iflag1 |= MYBIT(1, i); // Ack the interrupt by writing 1 to it
            sddf_dprintf("Timestamp: %u\n", control_regs->timer); // Read the timer to unlock the MB
            goto handled;
        }
    }

    for (int i = 0; i < 32; i++) { // iflag2 (mb32-63)
        if (MYBIT(1, i) & control_regs->iflag2) { // Check for the corresponding flag
            can_rx(i + 32); // read the corresponding message buffer
            control_regs->iflag2 |= MYBIT(1, i); // Ack the interrupt by writing 1 to it
            sddf_dprintf("Timestamp: %u\n", control_regs->timer); // Read the timer to unlock the MB
            goto handled;
        }
    }

    // Transmission complete interrupt
    if (MYBIT(1, 0) & control_regs->iflag1) {
        sddf_dprintf("Code following Tx: 0x%x", message_buffers->mb[0].can_ctrl); // Atm just reading this to see what it is -- expect 0x8 (INACTIVE)
        control_regs->iflag1 |= MYBIT(1, 0); // Ack the interrupt by writing 1 to it
        goto handled;
    }

    // TODO - ADD INTERRUPT HANDLING FOR OTHER SOURCES HERE (ERRORS / STATUS)

    // Ack the channel so we can receive more interrupts
    handled:
        microkit_irq_ack(ch);
}

// microkit init
void init (void) {
    sddf_dprintf("STARTING CAN DRIVER\n");
    can_init();

    // We expect at this point MB0 to be configured for Tx and the rest for Rx
    for (int i = 0; i < 64; i++) {
        sddf_dprintf("Message buffer: %d has control bits: %d, id bits: %d, data bits: %lu\n", i, message_buffers->mb[i].can_ctrl, message_buffers->mb[i].can_id, message_buffers->mb[i].data);
    }

    // sddf_dprintf("ESR1 register should be emtpy: %u\n", control_regs->esr1);

    // while (true) {
    //     sddf_dprintf("Waiting to sync...\n");
    //     sddf_dprintf("imask2 contents: %u\n", control_regs->imask2);    
    //     sddf_dprintf("timer contents: %u\n", control_regs->timer);    
    //     if (control_regs->esr1) {
    //         sddf_dprintf("esr1 status: %u\n", control_regs->esr1);    
    //         break;
    //     }
    // }


    // We expect that at this point we have no interrupts and no iflag masks are set
    // After our send we expect that mb0 will have an interrupt to indicate it has sent and probably mb1 will have one to indicate it has received this
    // transmission. Need to test this out
    can_tx();
}

// microkit notified
void notified(microkit_channel ch) {
    sddf_dprintf("INTERRUPT RECEIEVED!");
    handle_irq(ch);
}