/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// TOOD: fix the timeouts amounts i just chose 1s because i can

#include "ahci.h"
#include "pcie.h"

#include <microkit.h>
#include <sddf/blk/config.h>
#include <sddf/blk/queue.h>
#include <sddf/blk/storage_info.h>
#include <sddf/util/printf.h>
#include <sddf/util/string.h>
#include <sddf/timer/config.h>
#include <sddf/timer/client.h>

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_AHCI(...) do{ sddf_dprintf("AHCI |INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_AHCI(...) do{}while(0)
#endif

#define LOG_AHCI_ERR(...) do{ sddf_printf("AHCI |ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

#define fallthrough __attribute__((__fallthrough__))

blk_queue_handle_t blk_queue;

bool found_sata = false;

uint8_t sata_bus;
uint8_t sata_device;
uint8_t sata_function;

uint8_t ahci_port;
bool ahci_port_found = false;

int ahci_init_stage = 0;

uint8_t number_of_command_slots;

HBA_MEM* hba;

const uint64_t ahci_command_list_paddr = 0x60000000;
const uint64_t ahci_command_list_vaddr = 0x720000000;
const uint64_t ahci_command_list_size = 0x1000;

const uint64_t ahci_FIS_paddr = 0x60002000;
const uint64_t ahci_FIS_vaddr = 0x720002000;
const uint64_t ahci_FIS_size = 0x1000;

const uint64_t ahci_command_tables_paddr = 0x60004000;
const uint64_t ahci_command_tables_vaddr = 0x720004000;
const uint64_t ahci_command_tables_size = 0x2000;

const uint64_t data_region_paddr = 0x60080000;
const uint64_t data_region_vaddr = 0x720008000;
const uint64_t data_region_size = 0x10000;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t blk_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

// Find a free command list slot
int find_cmdslot(HBA_PORT *port)
{
    // If not set in SACT and CI, the slot is free
    // uint32_t slots = (port->sact | port->ci);
    uint32_t slots = (port->ci);

    for (int i=0; i< number_of_command_slots; i++)
    {
        if ((slots & 1) == 0)
            return i;
        slots >>= 1;
    }
    LOG_AHCI("Cannot find free command list entry\n");
    return -1;
}

// Start read/write command
// - Select an available command slot to use.
// - Setup command FIS.
// - Setup PRDT.
// - Setup command list entry.
// - Issue the command, and record separately that you have issued it.
bool read_device(HBA_PORT *port, uint32_t startl, uint32_t starth, uint32_t count, uint64_t buf)
{
    port->is = (uint32_t) -1; // Clear pending interrupt bits
    int slot = find_cmdslot(port);
    if (slot == -1) {
        return false;
    }

    LOG_AHCI("We are using cmdslot %d\n", slot);

    HBA_CMD_HEADER *cmdheader = (HBA_CMD_HEADER*)ahci_command_list_vaddr;
    cmdheader += slot;
    cmdheader->cfl = sizeof(FIS_REG_H2D)/sizeof(uint32_t);  // Command FIS size
    cmdheader->w = 0;       // Read from device
    cmdheader->prdtl = (uint16_t)((count-1)>>4) + 1;    // PRDT entries count

    if (cmdheader->prdtl > 8) {
        LOG_AHCI("We can't handle this request as its too big\n");
        return false;
    }

    HBA_CMD_TBL *cmdtbl = (HBA_CMD_TBL*)ahci_command_tables_vaddr;
    cmdtbl += slot;
    sddf_memset(cmdtbl, 0, sizeof(HBA_CMD_TBL) + (cmdheader->prdtl-1)*sizeof(HBA_PRDT_ENTRY));

    // 8K bytes (16 sectors) per PRDT
    for (int i=0; i<cmdheader->prdtl-1; i++)
    {
        cmdtbl->prdt_entry[i].dba = (uint32_t) (buf & 0xFFFFFFFF);
        cmdtbl->prdt_entry[i].dbau = (uint32_t) (buf >> 32);
        cmdtbl->prdt_entry[i].dbc = 8*1024-1;   // 8K bytes (this value should always be set to 1 less than the actual value)
        cmdtbl->prdt_entry[i].i = 1; // @Tristan: no interrupts for now
        buf += 8 * 1024;  // 4K words
        count -= 16;    // 16 sectors
    }
    // Last entry
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].dba = (uint32_t) (buf & 0xFFFFFFFF);;
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].dbau = (uint32_t) (buf >> 32);
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].dbc = (count<<9)-1;   // 512 bytes per sector
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].i = 0; // @Tristan: currently intterrupts are off

    // Setup command
    FIS_REG_H2D *cmdfis = (FIS_REG_H2D*)(&cmdtbl->cfis);

    cmdfis->fis_type = FIS_TYPE_REG_H2D;
    cmdfis->c = 1;  // Command
    cmdfis->command = ATA_CMD_READ_DMA_EX;

    cmdfis->lba0 = (uint8_t)startl;
    cmdfis->lba1 = (uint8_t)(startl>>8);
    cmdfis->lba2 = (uint8_t)(startl>>16);
    cmdfis->device = 1<<6;  // LBA mode

    cmdfis->lba3 = (uint8_t)(startl>>24);
    cmdfis->lba4 = (uint8_t)starth;
    cmdfis->lba5 = (uint8_t)(starth>>8);

    cmdfis->countl = count & 0xFF;
    cmdfis->counth = (count >> 8) & 0xFF;

    // The below loop waits until the port is no longer busy before issuing a new command
    int spin = 0;
    while ((port->tfd & (ATA_DEV_BUSY | ATA_DEV_DRQ)) && spin < 1000000)
    {
        spin++;
    }
    if (spin == 1000000)
    {
        LOG_AHCI("Port is hung\n");
        return false;
    }

    port->ci = 1<<slot; // Issue command

    // Wait for completion
    while (1)
    {
        // In some longer duration reads, it may be helpful to spin on the DPS bit
        // in the PxIS port field as well (1 << 5)
        if ((port->ci & (1<<slot)) == 0)
            break;
        if (port->is & HBA_PxIS_TFES)   // Task file error
        {
            LOG_AHCI("Read disk error\n");
            return false;
        }
    }

    // Check again
    if (port->is & HBA_PxIS_TFES)
    {
        LOG_AHCI("Read disk error\n");
        return false;
    }

    return true;
}

// Issue IDENTIFY DEVICE and extract sector size + total sectors.
// Returns true on success and fills out params.
bool identify_device(HBA_PORT *port, uint32_t *logical_sector_bytes_out, uint64_t *lba_count_out)
{
    if (!logical_sector_bytes_out || !lba_count_out) {
        return false;
    }

    port->is = (uint32_t)-1; // Clear pending interrupt bits
    int slot = find_cmdslot(port);
    if (slot == -1) {
        return false;
    }

    LOG_AHCI("We are using cmdslot %d\n", slot);

    // Command header for this slot
    HBA_CMD_HEADER *cmdheader = (HBA_CMD_HEADER*)ahci_command_list_vaddr;
    cmdheader += slot;
    cmdheader->cfl  = sizeof(FIS_REG_H2D)/sizeof(uint32_t); // Command FIS size
    cmdheader->w    = 0;       // Read from device
    cmdheader->prdtl = 1;      // We only need one PRDT entry for 512B

    LOG_AHCI("Command header interaction done\n");

    // Command table for this slot
    HBA_CMD_TBL *cmdtbl = (HBA_CMD_TBL*)ahci_command_tables_vaddr;
    cmdtbl += slot;
    sddf_memset(cmdtbl, 0, sizeof(HBA_CMD_TBL) + (cmdheader->prdtl-1)*sizeof(HBA_PRDT_ENTRY));

    // Single PRDT: 512 bytes for IDENTIFY DEVICE data
    cmdtbl->prdt_entry[0].dba  = (uint32_t)(data_region_paddr & 0xFFFFFFFF);
    cmdtbl->prdt_entry[0].dbau = (uint32_t)(data_region_paddr >> 32);
    cmdtbl->prdt_entry[0].dbc  = 512 - 1;  // byte count, value is (n-1)
    cmdtbl->prdt_entry[0].i    = 0;        // @Tristan: currently intterrupts are off

    LOG_AHCI("Command table prdt stuff done\n");

    // Setup command
    FIS_REG_H2D *cmdfis = (FIS_REG_H2D*)(&cmdtbl->cfis);

    cmdfis->fis_type = FIS_TYPE_REG_H2D;
    cmdfis->c        = 1;                   // Command
    cmdfis->command  = ATA_CMD_IDENTIFY;

    LOG_AHCI("Do command\n");


    // For IDENTIFY, all LBA/COUNT fields are zero; device register need not set LBA

    cmdfis->device = 0;

    LOG_AHCI("here\n");

    // The below loop waits until the port is no longer busy before issuing a new command
    int spin = 0;
    while ((port->tfd & (ATA_DEV_BUSY | ATA_DEV_DRQ)) && spin < 1000000) {
        spin++;
    }
    if (spin == 1000000) {
        LOG_AHCI("Port is hung\n");
        return false;
    }

    port->ci = 1u << slot; // Issue command

    LOG_AHCI("issued command\n");

    // Wait for completion
    while (1) {
        // In some longer duration reads, it may be helpful to spin on the DPS bit
        // in the PxIS port field as well (1 << 5)
        if ((port->ci & (1<<slot)) == 0)
            break;
        if (port->is & HBA_PxIS_TFES)   // Task file error
        {
            LOG_AHCI("Read disk error\n");
            return false;
        }
    }

    // Check again
    if (port->is & HBA_PxIS_TFES)
    {
        LOG_AHCI("Read disk error\n");
        return false;
    }

    LOG_AHCI("Command successful!\n");

    ATA_IDENTIFY* ata_identify_response = (ATA_IDENTIFY*)data_region_vaddr;

    // Logical sector bytes (default 512)
    uint32_t logical_bytes = 512;
    if (ata_identify_response->w106 & (1u << 12)) {
        uint32_t lss = ((uint32_t)ata_identify_response->logical_sector_size_hi << 16) | (uint32_t)ata_identify_response->logical_sector_size_lo;
        if (lss) {
            logical_bytes = lss;
        }
    }

    uint64_t lba_count;
    if (ata_identify_response->w83 & (1u << 10)) {
        lba_count  = (uint64_t)ata_identify_response->lba48_0;
        lba_count |= (uint64_t)ata_identify_response->lba48_1 << 16;
        lba_count |= (uint64_t)ata_identify_response->lba48_2 << 32;
        lba_count |= (uint64_t)ata_identify_response->lba48_3 << 48;
    } else {
        lba_count = (uint32_t)ata_identify_response->lba28_lo | ((uint32_t)ata_identify_response->lba28_hi << 16);
    }

    *logical_sector_bytes_out = logical_bytes;
    *lba_count_out = lba_count;

    LOG_AHCI("IDENTIFY: logical sector size = %u bytes, total sectors (LBA) = %llu, capacity = %llu bytes\n",
             logical_bytes, (unsigned long long)lba_count,
             (unsigned long long)(lba_count * (uint64_t)logical_bytes));

    return true;
}

// Start command engine
void start_cmd(HBA_PORT *port)
{
    LOG_AHCI("Starting command engine...\n");

    // Wait until CR (bit15) is cleared
    while (port->cmd & HBA_PxCMD_CR) {}

    // Set FRE (bit4) and ST (bit0)
    port->cmd |= HBA_PxCMD_FRE;
    port->cmd |= HBA_PxCMD_ST;

    // ChatGPT says this matters
    // port->cmd |= HBA_PxCMD_FRE;
    // while (!(port->cmd & HBA_PxCMD_FR)) {}
    // port->cmd |= HBA_PxCMD_ST;

     LOG_AHCI("Successfully started\n");
}

// Stop command engine
void stop_cmd(HBA_PORT *port)
{
    LOG_AHCI("Stopping command engine...\n");

    // Clear ST (bit0)
    port->cmd &= ~HBA_PxCMD_ST;

    // Clear FRE (bit4)
    port->cmd &= ~HBA_PxCMD_FRE;

    // Wait until FR (bit14), CR (bit15) are cleared
    while(1)
    {
        if (port->cmd & HBA_PxCMD_FR)
            continue;
        if (port->cmd & HBA_PxCMD_CR)
            continue;
        break;
    }

    LOG_AHCI("Successfully stopped\n");

}

// @Tristan: analyse this function how do we implement the resetting for the port
void port_reset_1(HBA_PORT *port) {
    // Engine must be stopped before we touch SCTL
    stop_cmd(port); // Stop command engine

    port->is   = 0xFFFFFFFF;
    port->serr = 0xFFFFFFFF;

    port->cmd |= HBA_PxCMD_SUD; // spin-up if needed // @Tristan: ?

    // COMRESET
    port->sctl = (port->sctl & ~0xF) | 0x1; // DET=1

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_MS);
}

void port_reset_2(HBA_PORT *port) {
    port->sctl &= ~0xF; // DET=0

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void port_reset_3(HBA_PORT *port) {
    if (((port->ssts & 0xF) != HBA_PORT_DET_PRESENT) ||
           (((port->ssts >> 8) & 0xF) != HBA_PORT_IPM_ACTIVE)) {
        LOG_AHCI("Something went wrong\n");
        assert(false);
    }

    port->is   = 0xFFFFFFFF;
    port->serr = 0xFFFFFFFF;
}

// We currently assume our system only uses one port
void port_rebase(HBA_PORT *port, int portno)
{
    assert((ahci_command_list_paddr & (1024 - 1)) == 0);  // CLB: 1 KiB
    assert((ahci_FIS_paddr          & (256  - 1)) == 0);  // FB : 256 B
    assert((ahci_command_tables_paddr & (256 - 1)) == 0); // CT : 256 B

    stop_cmd(port); // Stop command engine

    // Command list offset: 1K*portno
    // Command list entry size = 32
    // Command list entry maxim count = 32
    // Command list maxim size = 32*32 = 1K per port
    // port->clb = AHCI_BASE + (portno<<10); // If we want to cater to more

    port->clb  = (uint32_t)(ahci_command_list_paddr & 0xFFFFFFFF);
    port->clbu = (uint32_t)(ahci_command_list_paddr >> 32);
    sddf_memset((void*)ahci_command_list_vaddr, 0, 1024);
    LOG_AHCI("Cleared ahci_command_list_vaddr\n");

    // FIS offset: 32K+256*portno
    // FIS entry size = 256 bytes per port
    // port->fb = AHCI_BASE + (32<<10) + (portno<<8); // If we want to cater to more ports

    port->fb = (uint32_t)(ahci_FIS_paddr & 0xFFFFFFFF);
    port->fbu = (uint32_t)(ahci_FIS_paddr >> 32);
    sddf_memset((void*)ahci_FIS_vaddr, 0, 256);
    LOG_AHCI("Cleared ahci_FIS_vaddr\n");

    // Command table offset: 40K + 8K*portno
    // Command table size = 256*32 = 8K per port

    HBA_CMD_HEADER *cmdheader = (HBA_CMD_HEADER*)ahci_command_list_vaddr;
    for (int i=0; i<32; i++)
    {
        cmdheader[i].prdtl = 8; // 8 prdt entries per command table
        // 256 bytes per command table, 64+16+48+16*8
        // Command table offset: 40K + 8K*portno + cmdheader_index*256
        // cmdheader[i].ctba = AHCI_BASE + (40<<10) + (portno<<13) + (i<<8); // If we want to cater to more ports

        uint64_t paddr = ahci_command_tables_paddr + ((uint64_t)i << 8); // 1 << 8 = 256
        cmdheader[i].ctba = (uint32_t)(paddr & 0xFFFFFFFF);
        cmdheader[i].ctbau = (uint32_t)(paddr >> 32);

        uint64_t vaddr = ahci_command_tables_vaddr + ((uint64_t)i << 8);
        sddf_memset((void*)vaddr, 0, 256);
        LOG_AHCI("Cleared %d ahci_command_tables_vaddr\n", i);
    }

    start_cmd(port); // Start command engine

    // @Tristan: should we consider clearing erro interrupts ?
}

// Check device type
static int check_type(HBA_PORT *port)
{
    uint32_t ssts = port->ssts;

    uint8_t ipm = (ssts >> 8) & 0x0F;
    uint8_t det = ssts & 0x0F;

    if (det != HBA_PORT_DET_PRESENT)    // Check drive status
        return AHCI_DEV_NULL;
    if (ipm != HBA_PORT_IPM_ACTIVE)
        return AHCI_DEV_NULL;

    switch (port->sig)
    {
    case SATA_SIG_ATAPI:
        return AHCI_DEV_SATAPI;
    case SATA_SIG_SEMB:
        return AHCI_DEV_SEMB;
    case SATA_SIG_PM:
        return AHCI_DEV_PM;
    default:
        return AHCI_DEV_SATA;
    }
}

void probe_port()
{
    // Search disk in implemented ports
    uint32_t pi = hba->pi;
    int i = 0;
    while (i<32)
    {
        if (pi & 1)
        {
            int dt = check_type(&hba->ports[i]);
            if (dt == AHCI_DEV_SATA)
            {
                LOG_AHCI("SATA drive found at port %d\n", i);
                // We only handle the first device found.
                if (ahci_port_found == false) {
                    ahci_port = i;
                    ahci_port_found = true;
                }
            }
            else if (dt == AHCI_DEV_SATAPI)
            {
                LOG_AHCI("SATAPI drive found at port %d\n", i);
            }
            else if (dt == AHCI_DEV_SEMB)
            {
                LOG_AHCI("SEMB drive found at port %d\n", i);
            }
            else if (dt == AHCI_DEV_PM)
            {
                LOG_AHCI("PM drive found at port %d\n", i);
            }
            else
            {
                LOG_AHCI("No drive found at port %d\n", i);
            }
        }

        pi >>= 1;
        i ++;
    }
}

void validate_allocated_dma_paddr() {
    bool dma64 = (hba->cap & (1 << 31)) != 0;
    if (!dma64) {
        assert(data_region_paddr <= UINT32_MAX);
        assert(ahci_command_tables_paddr <= UINT32_MAX);
        assert(ahci_FIS_paddr <= UINT32_MAX);
        assert(ahci_command_list_paddr <= UINT32_MAX);
    }
}

void ahci_init_2();

// Pre BIOS/OS Handoff
static void ahci_boh_procedure_1()
{
    if ((hba->cap2 & 1u) == 0) {
        LOG_AHCI("BOH not supported, skipping handoff\n");
        ahci_init_2();
        return;
    }

    // If BIOS doesn't claim ownership, nothing to do.
    if ((hba->bohc & 1u) == 0) {
        LOG_AHCI("BIOS not owning controller, no handoff needed\n");
        ahci_init_2();
        return;
    }

    LOG_AHCI("Requesting OS ownership...\n");
    hba->bohc |= (1u << 1);

    // BIOS firmware should now, Clear BOS to 0 (releasing ownership).
    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

static void ahci_boh_procedure_2()
{
    if ((hba->bohc & 1u) != 0) {
        LOG_AHCI("BIOS still hasn't released!\n");
        LOG_AHCI("Proceed anyway; some firmwares ignore BOS or release implictly when we HBA reset\n");
        // might have to disable in the firmware?
    }

    // Clear any semaphore-change latched status
    hba->bohc = (1u << 2);

    LOG_AHCI("BIOS/OS handoff complete (BOS=%u, OS=%u)\n",
             !!(hba->bohc & 1u), !!(hba->bohc & (1u << 1)));
}

static void ahci_hba_reset_1()
{
    LOG_AHCI("Enabling AHCI mode...\n");
    hba->ghc |= (1u << 31);

    LOG_AHCI("Issuing Host Bus Adapter (HBA) reset...\n");
    hba->ghc |= 1u;

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

static void ahci_hba_reset_2()
{
    if (hba->ghc & 1u) {
        LOG_AHCI("Reset hasn't been complete, for now we fail but we could do everything manually...\n");
        assert(false);
    }

    // Spec: after HR clears, registers are reinitialized; AE may clear on some HBAs.
    hba->ghc |= (1u << 31);
    LOG_AHCI("HBA reset complete\n");
}

void ahci_num_cmd_slots() {
    number_of_command_slots = ((hba->cap >> 8) & 0x1Fu) + 1;
    LOG_AHCI("Number of command slots is %u\n", number_of_command_slots);
}

void ahci_init_1() {
    LOG_AHCI("== Starting AHCI initialisation (1)...\n");
    ahci_init_stage = 1;

    hba = (HBA_MEM*)ahci_abar_vaddr;

    LOG_AHCI("Doing BIOS/OS proceedure...\n");
    ahci_boh_procedure_1();
}

void ahci_init_2() {
    LOG_AHCI("== Continuing AHCI initialisation (2)...\n");
    ahci_init_stage = 2;

    LOG_AHCI("Continuing BIOS/OS proceedure...\n");
    ahci_boh_procedure_2();

    LOG_AHCI("Resetting AHCI HBA...\n");
    ahci_hba_reset_1();
}

void ahci_init_3() {
    LOG_AHCI("== Continuing AHCI initialisation (3)...\n");
    ahci_init_stage = 3;

    LOG_AHCI("Continuing resetting AHCI HBA...\n");
    ahci_hba_reset_2();

    LOG_AHCI("Detecting attached SATA devices...\n");
    probe_port();
    assert(ahci_port_found);

    LOG_AHCI("Checking if 64 bit DMA is supported...\n");
    validate_allocated_dma_paddr();

    LOG_AHCI("Checking the number of command slots/headers...\n");
    ahci_num_cmd_slots();

    LOG_AHCI("Resetting port...\n");
    port_reset_1(&hba->ports[ahci_port]);
}

void ahci_init_4() {
    LOG_AHCI("== Continuing AHCI initialisation (4)...\n");
    ahci_init_stage = 4;
    LOG_AHCI("Continuing resetting port...\n");
    port_reset_2(&hba->ports[ahci_port]);
}

void ahci_init_5() {
    LOG_AHCI("== Continuing AHCI initialisation (5)...\n");
    ahci_init_stage = 5;

    LOG_AHCI("Continuing resetting port...\n");
    port_reset_3(&hba->ports[ahci_port]);

    LOG_AHCI("AHCI port memory space initialisation...\n");
    LOG_AHCI("Rebasing port %d\n", ahci_port);
    port_rebase(&hba->ports[ahci_port], ahci_port);

    LOG_AHCI("Send IDENTIFY ATA command to connected drives. Get their sector size and count...\n");
    uint32_t sector_size = 0;
    uint64_t sector_count = 0;
    if (identify_device(&hba->ports[ahci_port], &sector_size, &sector_count)) {
        LOG_AHCI("IDENTIFY succeeded\n");
    } else {
        LOG_AHCI("IDENTIFY failed\n");
    }

    // After this we have done initialisation!
    // I think we just need to get reads and writes done
    // Then try to do interrupt handling
    while (1) {}

}

void notified(microkit_channel ch)
{
    // if (ch == device_resources.irqs[0].id) {
    //     handle_client(/* was_irq: */ true);
    //     microkit_irq_ack(ch);
    // } else
    if (ch == blk_config.virt.id) {
        LOG_AHCI("got the clients request\n");
    } else if (ch == timer_config.driver_id) {
        if (ahci_init_stage == 1) {
            ahci_init_2();
        } else if (ahci_init_stage == 2) {
            ahci_init_3();
        } else if (ahci_init_stage == 3) {
            ahci_init_4();
        } else if (ahci_init_stage == 4) {
            ahci_init_5();
        } else {
            LOG_AHCI("got impossible timer interrupt\n");
            assert(false);
        }
    } else {
        LOG_AHCI("notification on unknown channel: %d\n", ch);
        assert(false);
    }
}

void init()
{
    assert(device_resources_check_magic(&device_resources));
    assert(blk_config_check_magic(&blk_config));
    assert(timer_config_check_magic(&timer_config));

    /* Setup the sDDF block queue */
    blk_queue_init(&blk_queue, blk_config.virt.req_queue.vaddr, blk_config.virt.resp_queue.vaddr,
                   blk_config.virt.num_buffers);

    LOG_AHCI("Beginning driver initialisation...\n");
    pcie_init();

    assert(found_sata);

    print_pci_info(sata_bus, sata_device, sata_function, false);

    ahci_init_1();
}
