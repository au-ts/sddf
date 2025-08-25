/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

// TOOD: fix the timeouts amounts i just chose 1s because i can
// TODO: error messages
// TODO: so much checking
// PRDT lenggth
// 48 bit and 28 bit address not implemented in the reads and write
// TOODO : fix up the the struct vs base+ offset stuff
// TODO: we only handle one port for now
// they both interact with pcie

// TODO: driver_status = DrvStatusInactive; add these where appropriate? or assert(false) LOG_DRIVER_ERR("Failed to initialise SD card\n");

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

#define MAX_PRDT_ENTRIES     8
#define SECTORS_PER_PRDT     16             // 8 KiB / 512 B
#define MAX_SECTORS_PER_CMD  (MAX_PRDT_ENTRIES * SECTORS_PER_PRDT)  // 128

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

uint8_t ahci_port_number;
bool ahci_port_found = false;

int ahci_init_stage = 0; // @Tristan: make this an enum?

uint8_t number_of_command_slots;

/* Make sure to update drv_to_blk_status() as well */
typedef enum {
    DrvSuccess,
    DrvIrqWait,
    DrvErrorInternal,
} drv_status_t;

 int slot = -1;

#define SDDF_BLOCKS_TO_AHCI_BLOCKS (BLK_TRANSFER_SIZE / 512)

// TODO: dont hardcode it at 512
// uint64_t sddf_blocks_to_ahci_blocks() {
//     blk_storage_info_t *storage_info = blk_config.virt.storage_info.vaddr;
//     uint64_t ahci_block_size = storage_info->sector_size ;

//     assert(BLK_TRANSFER_SIZE % ahci_block_size == 0);
//     return BLK_TRANSFER_SIZE / ahci_block_size;
//     // hopefully they devide nice
// }

HBA_MEM* hba;
HBA_PORT* port;
ATA_IDENTIFY* identify_command;
blk_storage_info_t *storage_info;

// i dont think they have setvar in sdfgen???
const uint64_t ahci_command_list_paddr = 0x10000000;
const uint64_t ahci_command_list_vaddr = 0x720000000;
const uint64_t ahci_command_list_size = 0x1000;

const uint64_t ahci_FIS_paddr = 0x10002000;
const uint64_t ahci_FIS_vaddr = 0x720002000;
const uint64_t ahci_FIS_size = 0x1000;

const uint64_t ahci_command_tables_paddr = 0x10004000;
const uint64_t ahci_command_tables_vaddr = 0x720004000;
const uint64_t ahci_command_tables_size = 0x2000;

const uint64_t data_region_paddr = 0x10008000;
const uint64_t data_region_vaddr = 0x720008000;
const uint64_t data_region_size = 0x10000;

const uint64_t identify_command_paddr = 0x10020000;
const uint64_t identify_command_vaddr = 0x720020000;
const uint64_t identify_command_size = 0x1000;

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t blk_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

/* The current action-status of the driver */
static enum {
    DrvStatusInactive,
    DrvStatusBringup,
    DrvStatusActive,
} driver_status;

typedef enum {
    RequestStateStart,
    RequestStateFinish,
} request_state_t;

static struct driver_state {
    struct {
        bool inflight;
        uint32_t id;
        blk_req_code_t code;
        uintptr_t paddr;
        uint64_t blk_number;
        uint16_t blk_count;
    } blk_req;

    request_state_t request_state;

} driver_state;

// Find a free command list slot
int find_cmdslot() {
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

// The code example shows how to read/write "count" sectors from sector offset "starth:startl" to "buf" with LBA48 mode from HBA "port".
// Every PRDT entry contains 8K bytes data payload at most.
// Start read/write command
// - Select an available command slot to use.
// - Setup command FIS.
// - Setup PRDT.
// - Setup command list entry.
// - Issue the command, and record separately that you have issued it. TODO: @Tristan
bool read_device(uint32_t startl, uint32_t starth, uint32_t count, uint64_t buf) {
    port->is = (uint32_t) -1; // Clear pending interrupt bits
     slot = find_cmdslot();
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
        cmdtbl->prdt_entry[i].i = 0; // @Tristan: no interrupts for now
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
    // while (1)
    // {
    //     // In some longer duration reads, it may be helpful to spin on the DPS bit
    //     // in the PxIS port field as well (1 << 5)
    //     if ((port->ci & (1<<slot)) == 0)
    //         break;
    //     if (port->is & HBA_PxIS_TFES)   // Task file error
    //     {
    //         LOG_AHCI("Read disk error\n");
    //         return false;
    //     }
    // }

    // // Check again
    // if (port->is & HBA_PxIS_TFES)
    // {
    //     LOG_AHCI("Read disk error\n");
    //     return false;
    // }

    return true;
}

bool write_device(uint32_t startl, uint32_t starth, uint32_t count, uint64_t buf) {
    port->is = (uint32_t) -1; // Clear pending interrupt bits
    slot = find_cmdslot();
    if (slot == -1) {
        return false;
    }

    LOG_AHCI("We are using cmdslot %d\n", slot);

    HBA_CMD_HEADER *cmdheader = (HBA_CMD_HEADER*)ahci_command_list_vaddr;
    cmdheader += slot;
    cmdheader->cfl   = sizeof(FIS_REG_H2D)/sizeof(uint32_t);  // Command FIS size
    cmdheader->w     = 1;       // Write to device
    cmdheader->prdtl = (uint16_t)((count-1)>>4) + 1;          // PRDT entries count

    if (cmdheader->prdtl > 8) {
        LOG_AHCI("We can't handle this request as its too big\n");
        return false;
    }

    HBA_CMD_TBL *cmdtbl = (HBA_CMD_TBL*)ahci_command_tables_vaddr;
    cmdtbl += slot;
    sddf_memset(cmdtbl, 0, sizeof(HBA_CMD_TBL) + (cmdheader->prdtl-1)*sizeof(HBA_PRDT_ENTRY));

    // 8K bytes (16 sectors) per PRDT is what we chose
    for (int i = 0; i < cmdheader->prdtl - 1; i++)
    {
        cmdtbl->prdt_entry[i].dba  = (uint32_t) (buf & 0xFFFFFFFF);
        cmdtbl->prdt_entry[i].dbau = (uint32_t) (buf >> 32);
        cmdtbl->prdt_entry[i].dbc  = 8*1024 - 1;   // 8K bytes (value is size-1)
        cmdtbl->prdt_entry[i].i    = 0;            // @Tristan: no interrupts for now
        buf   += 8 * 1024;  // 4K words
        count -= 16;        // 16 sectors
    }
    // Last entry
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].dba  = (uint32_t) (buf & 0xFFFFFFFF);
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].dbau = (uint32_t) (buf >> 32);
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].dbc  = (count << 9) - 1;   // 512 bytes per sector
    cmdtbl->prdt_entry[cmdheader->prdtl - 1].i    = 0; // @Tristan: currently interrupts are off

    // Setup command
    FIS_REG_H2D *cmdfis = (FIS_REG_H2D*)(&cmdtbl->cfis);

    cmdfis->fis_type = FIS_TYPE_REG_H2D;
    cmdfis->c        = 1;  // Command
    cmdfis->command  = ATA_CMD_WRITE_DMA_EX;

    cmdfis->lba0   = (uint8_t) startl;
    cmdfis->lba1   = (uint8_t) (startl >> 8);
    cmdfis->lba2   = (uint8_t) (startl >> 16);
    cmdfis->device = 1 << 6;  // LBA mode

    cmdfis->lba3 = (uint8_t) (startl >> 24);
    cmdfis->lba4 = (uint8_t) starth;
    cmdfis->lba5 = (uint8_t) (starth >> 8);

    cmdfis->countl = count & 0xFF;
    cmdfis->counth = (count >> 8) & 0xFF;

    // Wait while port is busy
    int spin = 0;
    while ((port->tfd & (ATA_DEV_BUSY | ATA_DEV_DRQ)) && spin < 1000000)
        spin++;
    if (spin == 1000000)
    {
        LOG_AHCI("Port is hung\n");
        return false;
    }

    port->ci = 1 << slot; // Issue command

    // // Wait for completion
    // while (1)
    // {
    //     if ((port->ci & (1 << slot)) == 0)
    //         break;
    //     if (port->is & HBA_PxIS_TFES)   // Task file error
    //     {
    //         LOG_AHCI("Write disk error\n");
    //         return false;
    //     }
    // }

    // // Check again
    // if (port->is & HBA_PxIS_TFES)
    // {
    //     LOG_AHCI("Write disk error\n");
    //     return false;
    // }

    return true;
}

// TODO: @Tristan: fix this shit THESE dont validate size or anything
bool ahci_write_blocks(uintptr_t dma_address, uint64_t sector_number, uint64_t sector_count) {
    // drv_status_t status;
    // uint32_t data_address;
    switch (driver_state.request_state) {
    case RequestStateStart: {
        // convert to write_device
        uint32_t this_count = (sector_count > MAX_SECTORS_PER_CMD)
                                  ? MAX_SECTORS_PER_CMD
                                  : (uint32_t)sector_count;

        uint64_t lba        = sector_number;
        uint32_t startl     = (uint32_t)(lba & 0xFFFFFFFFull);
        uint32_t starth     = (uint32_t)((lba >> 32) & 0xFFFFull);

        bool success = write_device(startl, starth, this_count, (uint64_t)dma_address);
        if (!success) {
            return DrvErrorInternal;
        }

        driver_state.request_state = RequestStateFinish;
        return DrvIrqWait;
    }

    case RequestStateFinish:
        // We got the response

        // Error first
        if (port->is & (1u << 30)) {
            port->is = (1u << 30);   // W1C clear
            hba->is  = (1u << ahci_port_number);
            driver_state.request_state = RequestStateStart;
            return DrvErrorInternal;
        }

        // Not done yet?
        if ((port->is & (1u << 0)) == 0) {
            return DrvErrorInternal;
        }

        // FIS arrived; make sure our slot’s CI bit is now cleared
        if (slot >= 0 && (port->ci & (1u << slot)) != 0) {
            // command not fully completed yet; keep waiting
            return DrvErrorInternal;
        }

        // Ack the completion we handled
        port->is = ((1u << 0) | (1u << 30));                        // per-port W1C
        hba->is  = (1u << ahci_port_number);   // HBA summary W1C

        LOG_AHCI("command complete (IRQ)\n");
        driver_state.request_state = RequestStateStart;
        slot = -1;

        return DrvSuccess;

    default:
        /* unreachable */
        return DrvIrqWait;
    }
}

bool ahci_read_blocks(uintptr_t dma_address, uint64_t sector_number, uint64_t sector_count) {
    // drv_status_t status;
    // uint32_t data_address;
    switch (driver_state.request_state) {
    case RequestStateStart: {
        uint32_t this_count = (sector_count > MAX_SECTORS_PER_CMD)
                              ? MAX_SECTORS_PER_CMD
                              : (uint32_t)sector_count;

        uint64_t lba        = sector_number;
        uint32_t startl     = (uint32_t)(lba & 0xFFFFFFFFull);
        uint32_t starth     = (uint32_t)((lba >> 32) & 0xFFFFull);

        bool success = read_device (startl, starth, this_count, (uint64_t)dma_address);
        if (!success) {
            return DrvErrorInternal;
        }

        driver_state.request_state = RequestStateFinish;
        return DrvIrqWait;
    }
    case RequestStateFinish:
        // We got the response

        // Error first
        if (port->is & (1u << 30)) {
            port->is = (1u << 30);   // W1C clear
            hba->is  = (1u << ahci_port_number);
            driver_state.request_state = RequestStateStart;
            return DrvErrorInternal;
        }

        // Not done yet?
        if ((port->is & (1u << 0)) == 0) {
            return DrvErrorInternal;
        }

        // FIS arrived; make sure our slot’s CI bit is now cleared
        if (slot >= 0 && (port->ci & (1u << slot)) != 0) {
            // command not fully completed yet; keep waiting
            return DrvErrorInternal;
        }

        // Ack the completion we handled
        port->is = ((1u << 0) | (1u << 30));                        // per-port W1C
        hba->is  = (1u << ahci_port_number);   // HBA summary W1C

        LOG_AHCI("command complete (IRQ)\n");
        driver_state.request_state = RequestStateStart;
        slot = -1;

        return DrvSuccess;

    default:
        /* unreachable */
        return DrvIrqWait;
    }
}

// THIS WILL NOT WORK BECAUSE UNLESS INTERUPTS ARE OFF
// void test_generic_reads_and_writes() {
//     LOG_AHCI("Testing Generic reads and writes\n");

//     uint8_t *write_buf = (uint8_t*)data_region_vaddr;
//     uint8_t *read_buf  = (uint8_t*)(data_region_vaddr + 0x5000);

//     LOG_AHCI("Filling our memory!\n");
//     // Fill the 512-byte sector with repeating alphabet
//     {
//         uint8_t *buf = write_buf;
//         for (int i = 0; i < 512; i++) {
//             buf[i] = 'A' + (i % 26);
//         }
//     }

//     LOG_AHCI("Now doing a generic write!\n");
//     if (write_device(100, 0, 1, data_region_paddr)) {
//         LOG_AHCI("write succeeded\n");
//     } else {
//         LOG_AHCI("write failed\n");
//     }

//     LOG_AHCI("Now doing a generic read!\n");
//     if (read_device(100, 0, 1, data_region_paddr + 0x5000)) {
//         LOG_AHCI("read succeeded\n");
//     } else {
//         LOG_AHCI("read failed\n");
//     }

//     LOG_AHCI("Checking if they match!\n");
//     bool match = true;
//     for (int i = 0; i < 512; i++) {
//         if (write_buf[i] != read_buf[i]) {
//             LOG_AHCI("Mismatch at byte %d: wrote 0x%02x, read 0x%02x\n",
//                      i, write_buf[i], read_buf[i]);
//             match = false;
//             break;
//         }
//     }

//     if (match) {
//         LOG_AHCI("Readback matches written pattern!\n");
//     } else {
//         LOG_AHCI("Readback did not match!\n");
//     }
// }

// TODO: @Tristan: this shouldn't even get called
void handle_client_device_inactive(void) {
    while (!blk_queue_empty_req(&blk_queue)) {
        blk_req_code_t code;
        uintptr_t paddr;
        uint64_t block_number;
        uint16_t count;
        uint32_t id;
        int err = blk_dequeue_req(&blk_queue, &code, &paddr, &block_number, &count, &id);
        assert(!err); /* shouldn't be empty */

        err = blk_enqueue_resp(&blk_queue, BLK_RESP_ERR_NO_DEVICE, 0, id);
        if (err) {
            /* response queue is full */
            break;
        }
    }

    microkit_notify(blk_config.virt.id);
}

// For now do 1 request at a time
void handle_client(bool was_irq) {
    assert(!(driver_status == DrvStatusBringup));

    if (was_irq == false) {
        if (driver_state.blk_req.inflight) {
            /* Only handle block queue notifications when idle */
            return;
        }

        // /* if we're inactive (by choice or by recognition),
        //    or if there's no card (but we haven't yet propagated this change to the state) */
        // if (driver_status == DrvStatusInactive) {
        //     handle_client_device_inactive(); // TODO: can we even reach this?
        //     return;
        // }

        int err = blk_dequeue_req(&blk_queue, &driver_state.blk_req.code, &driver_state.blk_req.paddr,
                                      &driver_state.blk_req.blk_number, &driver_state.blk_req.blk_count,
                                      &driver_state.blk_req.id);

        if (err == -1) {
            /* no client requests; we likely handled it already.
               this can happen as we can dequeue outstanding requests following an
               IRQ being handled, which might happen before we get the virtualiser
               notification from the microkit event loop. */
            return;
        }

        driver_state.blk_req.inflight = true;
        LOG_AHCI("Received command: code=%d, paddr=0x%lx, block_number=%lu, count=%d, id=%d\n",
                       driver_state.blk_req.code, driver_state.blk_req.paddr, driver_state.blk_req.blk_number,
                       driver_state.blk_req.blk_count, driver_state.blk_req.id);

    }

    /* Should never get IRQs without inflight requests */
    if (!driver_state.blk_req.inflight) {
        assert(false);
    }

    blk_resp_status_t response_status;
    uint16_t success_count;

    switch (driver_state.blk_req.code) {
    case BLK_REQ_FLUSH:
    case BLK_REQ_BARRIER:
        /* No-ops. Because we only do 1 request at a time */
        response_status = BLK_RESP_OK;
        success_count = 0;
        break;

    case BLK_REQ_READ: {
        drv_status_t status = ahci_read_blocks(driver_state.blk_req.paddr,
                                                driver_state.blk_req.blk_number * SDDF_BLOCKS_TO_AHCI_BLOCKS,
                                                driver_state.blk_req.blk_count * SDDF_BLOCKS_TO_AHCI_BLOCKS);
        if (status == DrvIrqWait) {
            return;
        }

        response_status = (status == DrvSuccess) ? BLK_RESP_OK : BLK_RESP_ERR_UNSPEC; // random error message
        success_count = driver_state.blk_req.blk_count;
        break;
    }

    case BLK_REQ_WRITE: {
        drv_status_t status = ahci_write_blocks(driver_state.blk_req.paddr,
                                                 driver_state.blk_req.blk_number * SDDF_BLOCKS_TO_AHCI_BLOCKS,
                                                 driver_state.blk_req.blk_count * SDDF_BLOCKS_TO_AHCI_BLOCKS);
        if (status == DrvIrqWait) {
            return;
        }

        response_status = (status == DrvSuccess) ? BLK_RESP_OK : BLK_RESP_ERR_UNSPEC; // random error message
        success_count = driver_state.blk_req.blk_count;
        break;
    }

    default: {
        success_count = 0;
        response_status = BLK_RESP_ERR_INVALID_PARAM;
        break;
    }
    }

    int err = blk_enqueue_resp(&blk_queue, response_status, success_count, driver_state.blk_req.id);
    assert(!err);
    LOG_AHCI("Enqueued response: status=%d, success_count=%d, id=%d\n", response_status, success_count,
               driver_state.blk_req.id);
    microkit_notify(blk_config.virt.id);

    driver_state.blk_req.inflight = false;

    /* Tail-call to handle another request */
    return handle_client(false);
}

// INIT STAGE

bool identify_device_1() {
    port->is = (uint32_t)-1; // Clear pending interrupt bits
    slot = find_cmdslot();
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
    cmdtbl->prdt_entry[0].dba  = (uint32_t)(identify_command_paddr & 0xFFFFFFFF);
    cmdtbl->prdt_entry[0].dbau = (uint32_t)(identify_command_paddr >> 32);
    cmdtbl->prdt_entry[0].dbc  = 512 - 1;  // byte count, value is (n-1) // IDENTIFY DEVICE payload is always 512 bytes by spec—independent of the drive’s logical sector size.
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

    /* force the MMIO write to post; a readback is enough */
    for (int i = 0; i < 1000; i++) {
        uint32_t r = port->ci;
        if (r & (1u << slot)) {
            LOG_AHCI("CI latched: 0x%08x\n", r);
            break;
        }
    }

    LOG_AHCI("Issued command\n");
    LOG_AHCI("Issued: PxCI=0x%08x PxCMD=0x%08x GHC=0x%08x\n",
         port->ci, port->cmd, hba->ghc);

    // sddf_timer_set_timeout(timer_config.driver_id, 3 * NS_IN_S);

    return true;
}

bool identify_device_2() {
    /* Snapshot once so we act on a consistent view */
    uint32_t is = port->is;

    /* --- Error first (TFES) --- */
    if (is & (1u << 30)) {
        port->is = (1u << 30);                 /* W1C TFES */
        hba->is  = (1u << ahci_port_number);   /* W1C HBA summary for this port */
        LOG_AHCI("IDENTIFY: task file error (PxTFD=0x%08x PxIS=0x%08x)\n", port->tfd, is);
        return false;
    }

    /* --- Completion for IDENTIFY can be PSS and/or SDBS and/or DHRS --- */
    const uint32_t done_mask = (1u << 0) | (1u << 1) | (1u << 3); /* DHRS | PSS | SDBS */
    if ((is & done_mask) == 0) {
        return false;  /* not done yet */
    }

    /* Command must be fully completed: CI bit cleared */
    if (slot >= 0 && (port->ci & (1u << slot)) != 0) {
        return false;  /* still in-flight */
    }

    /* Data is ready in PRDT buffer */
    identify_command = (ATA_IDENTIFY *)identify_command_vaddr;

    /* --- Acknowledge everything we handled --- */
    uint32_t clr = is & ((1u << 0) | (1u << 1) | (1u << 3) | (1u << 30)); /* DHRS|PSS|SDBS|TFES */
    if (clr) {
        port->is = clr;                         /* W1C per-port causes */
        hba->is  = (1u << ahci_port_number);    /* W1C summary bit for this port */
    }

    LOG_AHCI("IDENTIFY complete; PxIS was 0x%08x, cleared 0x%08x (via %s%s%s)\n",
             is, clr,
             (is & (1u<<0)) ? "DHRS " : "",
             (is & (1u<<1)) ? "PSS "  : "",
             (is & (1u<<3)) ? "SDBS " : "");
    return true;
}

void ata_extract_serial(char *dst) {
    const uint16_t *src = (const uint16_t *)(identify_command->w0_59 + 10); // words 10–19
    for (int i = 0; i < 10; i++) {
        dst[2*i]     = src[i] >> 8;    // high byte first
        dst[2*i + 1] = src[i] & 0xFF;  // then low byte
    }
    dst[20] = '\0';
}

void setup_blk_storage_info_1() {
    LOG_AHCI("Send IDENTIFY ATA command to connected drives. Get their sector size and count...\n");
    if (identify_device_1()) {
        LOG_AHCI("Initial part went correctly\n");
    } else {
        LOG_AHCI("something failed\n");
        assert(false);
    }
}

void setup_blk_storage_info_2() {
    if (identify_device_2()) {
        LOG_AHCI("Second part went correctly\n");
    } else {
        LOG_AHCI("something failed\n");
        assert(false);
    }

    storage_info = blk_config.virt.storage_info.vaddr;

    assert(!storage_info->ready);

    ata_extract_serial(storage_info->serial_number);

    if (identify_command->w106 & (1 << 12)) {
        storage_info->sector_size =
            identify_command->logical_sector_size_lo |
            (identify_command->logical_sector_size_hi << 16);
    } else {
        storage_info->sector_size = 512; // default
    }

    // Block size
    storage_info->block_size = 1; // copy the other blk device // this is the optimal amount
    // jsut make it 1 for now we can always change it

    // Queue depth
    // storage_info->queue_depth = ?;
    /*
    uint16_t device_depth = ncq_supported ? ((identify->queue_depth & 0x1F) + 1) : 1;
    uint16_t hba_slots    = ((ahci->CAP >> 8) & 0x1F) + 1;   // CAP.NCS (bits 12:8) + 1
    uint16_t driver_cap   = DRIVER_QUEUE_LIMIT;              // your policy, e.g., 32

    storage_info->queue_depth = MIN3(device_depth, hba_slots, driver_cap);

    i think  its just the command header length
    */

    // Geometry (legacy CHS)
    storage_info->cylinders = identify_command->w0_59[1];
    storage_info->heads     = identify_command->w0_59[3];
    storage_info->blocks    = identify_command->w0_59[6];

    // Capacity in sectors (prefer 48-bit if supported)
    uint64_t sectors;
    if (identify_command->w83 & (1 << 10)) {
        sectors = ((uint64_t)identify_command->lba48_3 << 48) |
                  ((uint64_t)identify_command->lba48_2 << 32) |
                  ((uint64_t)identify_command->lba48_1 << 16) |
                   (uint64_t)identify_command->lba48_0;
    } else {
        sectors = ((uint32_t)identify_command->lba28_hi << 16) |
                   identify_command->lba28_lo;
    }
    storage_info->capacity = sectors * storage_info->sector_size / BLK_TRANSFER_SIZE;

     // Assume writable unless tested otherwise // we dont support CD-ROM's????
    storage_info->read_only = false; // TODO: fix

    LOG_AHCI("Drive size (blocks): %lu\n", storage_info->capacity);
    blk_storage_set_ready(storage_info, true);
}

// Start command engine
void start_cmd() {
    LOG_AHCI("Starting command engine...\n");

    // Wait until CR (bit15) is cleared
    while (port->cmd & HBA_PxCMD_CR) {}

    // Set FRE (bit4) and ST (bit0)
    // port->cmd |= HBA_PxCMD_FRE;
    // port->cmd |= HBA_PxCMD_ST;

    port->cmd |= HBA_PxCMD_FRE;
    while (!(port->cmd & HBA_PxCMD_FR)) {}
    port->cmd |= HBA_PxCMD_ST;

    LOG_AHCI("Successfully started\n");
}

// Stop command engine
void stop_cmd() {
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

void enable_irqs() {
    // Clear latched global + this port (W1C)
    hba->is = 0xFFFFFFFF;
    port->is = 0xFFFFFFFF;

    // AHCI Enable + Global Interrupt Enable
    hba->ghc |= (1u << 31); // AE
    hba->ghc |= (1u << 1);  // IE

    // Enable just what you need: command-complete + task-file error
    // port->ie = (1u << 0) | (1u << 30) | (1u << 3); // also PIO setup apparently
    port->ie = (1u<<0) | (1u<<1) | (1u<<3) | (1u<<30); // DHRS + PSS + SDBS + TFES

}

void port_rebase() {
    assert((ahci_command_list_paddr & (1024 - 1)) == 0);  // CLB: 1 KiB
    assert((ahci_FIS_paddr          & (256  - 1)) == 0);  // FB : 256 B
    assert((ahci_command_tables_paddr & (256 - 1)) == 0); // CT : 256 B

    stop_cmd(); // Stop command engine

    // Command list offset: 1K*portno
    // Command list entry size = 32
    // Command list entry maxim count = 32
    // Command list maxim size = 32*32 = 1K per port
    // port->clb = AHCI_BASE + (portno<<10); // If we want to cater to more

    port->clb  = (uint32_t)(ahci_command_list_paddr & 0xFFFFFFFF);
    port->clbu = (uint32_t)(ahci_command_list_paddr >> 32);
    sddf_memset((void*)ahci_command_list_vaddr, 0, 1024); // here
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

    start_cmd(); // Start command engine

    // @Tristan: should we consider clearing erro interrupts ?
}

void port_reset_1() {
    // Engine must be stopped before we touch SCTL
    stop_cmd(); // Stop command engine

    port->is   = 0xFFFFFFFF;
    port->serr = 0xFFFFFFFF;

    port->cmd |= HBA_PxCMD_SUD; // spin-up if needed // @Tristan: ?

    // COMRESET
    port->sctl = (port->sctl & ~0xF) | 0x1; // DET=1

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_MS);
}

void port_reset_2() {
    port->sctl &= ~0xF; // DET=0

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void port_reset_3() {
    if (((port->ssts & 0xF) != HBA_PORT_DET_PRESENT) ||
           (((port->ssts >> 8) & 0xF) != HBA_PORT_IPM_ACTIVE)) {
        LOG_AHCI("Something went wrong\n");
        assert(false);
    }

    port->is   = 0xFFFFFFFF;
    port->serr = 0xFFFFFFFF;
}

void ahci_num_cmd_slots() {
    number_of_command_slots = ((hba->cap >> 8) & 0x1Fu) + 1;
    LOG_AHCI("Number of command slots is %u\n", number_of_command_slots);
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

int check_type(HBA_PORT *port_to_check) {
    uint32_t ssts = port_to_check->ssts;

    uint8_t ipm = (ssts >> 8) & 0x0F;
    uint8_t det = ssts & 0x0F;

    if (det != HBA_PORT_DET_PRESENT)    // Check drive status
        return AHCI_DEV_NULL;
    if (ipm != HBA_PORT_IPM_ACTIVE)
        return AHCI_DEV_NULL;

    switch (port_to_check->sig)
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

void probe_port() {
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
                    ahci_port_number = i;
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

void ahci_hba_reset_1() {
    LOG_AHCI("Enabling AHCI mode...\n");
    hba->ghc |= (1u << 31);

    LOG_AHCI("Issuing Host Bus Adapter (HBA) reset...\n");
    hba->ghc |= 1u;

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void ahci_hba_reset_2() {
    if (hba->ghc & 1u) {
        LOG_AHCI("Reset hasn't been complete, for now we fail but we could do everything manually...\n");
        assert(false);
    }

    // Spec: after HR clears, registers are reinitialized; AE may clear on some HBAs.
    hba->ghc |= (1u << 31);
    LOG_AHCI("HBA reset complete\n");
}

void ahci_boh_procedure_1() {
    if ((hba->cap2 & 1u) == 0) {
        LOG_AHCI("BOH not supported, skipping handoff\n");
        // To help with control flow we just do timeout still
    } else if ((hba->bohc & 1u) == 0) {
        LOG_AHCI("BIOS not owning controller, no handoff needed\n");
        // To help with control flow we just do timeout still
    } else {
        LOG_AHCI("Requesting OS ownership...\n");
        hba->bohc |= (1u << 1);
        // BIOS firmware should now, Clear BOS to 0 (releasing ownership).
    }

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void ahci_boh_procedure_2() {
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

void ahci_init_1() {
    LOG_AHCI("== Starting AHCI initialisation (1)...\n");

    hba = (HBA_MEM*)ahci_abar_vaddr;

    LOG_AHCI("Doing BIOS/OS handoff proceedure...\n");
    ahci_boh_procedure_1();
}

void ahci_init_2() {
    LOG_AHCI("== Continuing AHCI initialisation (2)...\n");

    LOG_AHCI("Continuing BIOS/OS proceedure...\n");
    ahci_boh_procedure_2();

    LOG_AHCI("Resetting AHCI HBA...\n");
    ahci_hba_reset_1();
}

void ahci_init_3() {
    LOG_AHCI("== Continuing AHCI initialisation (3)...\n");

    LOG_AHCI("Continuing resetting AHCI HBA...\n");
    ahci_hba_reset_2();

    LOG_AHCI("Detecting attached SATA devices...\n");
    probe_port();

    assert(ahci_port_found);

    LOG_AHCI("Choosing port %d...\n", ahci_port_number);

    port = &hba->ports[ahci_port_number];

    LOG_AHCI("Checking if physical addresses are valid for DMA...\n");
    validate_allocated_dma_paddr();

    LOG_AHCI("Checking the number of command slots/headers...\n");
    ahci_num_cmd_slots();

    LOG_AHCI("Resetting port...\n");
    port_reset_1();
}

void ahci_init_4() {
    LOG_AHCI("== Continuing AHCI initialisation (4)...\n");

    LOG_AHCI("Continuing resetting port...\n");
    port_reset_2();
}

void ahci_init_5() {
    LOG_AHCI("== Continuing AHCI initialisation (5)...\n");

    LOG_AHCI("Continuing resetting port...\n");
    port_reset_3();

    LOG_AHCI("AHCI port memory space initialisation...\n");
    LOG_AHCI("Rebasing port %d\n", ahci_port_number);
    port_rebase();

    LOG_AHCI("Enabling interrupts for port %u...\n", ahci_port_number);
    enable_irqs();

    // DMA successfully works!
    // test_generic_reads_and_writes();

    LOG_AHCI("Setting up blk storage info...\n");
    setup_blk_storage_info_1();
}

void ahci_init_6() {
    LOG_AHCI("== Continuing AHCI initialisation (5)...\n");

    LOG_AHCI("Continuing setting up blk storage info...\n");
    setup_blk_storage_info_2();

    // get rid of useuless irqs
    port->ie = 0;
    port->ie = (1u << 0) | (1u << 30);
    LOG_AHCI("Driver initialisation complete\n");
}

void dump_ahci_registers() {
    /* ===== HBA (global) registers — per your HBA_MEM layout ===== */
    uint32_t cap      = hba->cap;       /* 0x00 */
    uint32_t ghc      = hba->ghc;       /* 0x04 */
    uint32_t hba_is   = hba->is;        /* 0x08 */
    uint32_t pi       = hba->pi;        /* 0x0C */
    uint32_t vs       = hba->vs;        /* 0x10 */
    uint32_t ccc_ctl  = hba->ccc_ctl;   /* 0x14 */
    uint32_t ccc_pts  = hba->ccc_pts;   /* 0x18 */
    uint32_t em_loc   = hba->em_loc;    /* 0x1C */
    uint32_t em_ctl   = hba->em_ctl;    /* 0x20 */
    uint32_t cap2     = hba->cap2;      /* 0x24 */
    uint32_t bohc     = hba->bohc;      /* 0x28 */

    LOG_AHCI("=== AHCI HBA Reg Dump ===\n");
    LOG_AHCI("CAP=0x%08x  GHC=0x%08x  IS=0x%08x  PI=0x%08x  VS=0x%08x\n",
             cap, ghc, hba_is, pi, vs);
    LOG_AHCI("CCC_CTL=0x%08x  CCC_PTS=0x%08x  EM_LOC=0x%08x  EM_CTL=0x%08x\n",
             ccc_ctl, ccc_pts, em_loc, em_ctl);
    LOG_AHCI("CAP2=0x%08x  BOHC=0x%08x\n", cap2, bohc);

    /* ===== Per-port registers — dump all ports indicated in PI ===== */
    LOG_AHCI("=== Per-Port Reg Dump (PI=0x%08x) ===\n", pi);
    for (int i = 0; i < 1; i++) {
        if (!(pi & (1u << i))) continue;

        volatile HBA_PORT *p = &hba->ports[i];

        uint32_t clb    = p->clb;     /* 0x00 */
        uint32_t clbu   = p->clbu;    /* 0x04 */
        uint32_t fb     = p->fb;      /* 0x08 */
        uint32_t fbu    = p->fbu;     /* 0x0C */
        uint32_t pis    = p->is;      /* 0x10 */
        uint32_t pie    = p->ie;      /* 0x14 */
        uint32_t cmd    = p->cmd;     /* 0x18 */
        uint32_t rsv0   = p->rsv0;    /* 0x1C */
        uint32_t tfd    = p->tfd;     /* 0x20 */
        uint32_t sig    = p->sig;     /* 0x24 */
        uint32_t ssts   = p->ssts;    /* 0x28 */
        uint32_t sctl   = p->sctl;    /* 0x2C */
        uint32_t serr   = p->serr;    /* 0x30 */
        uint32_t sact   = p->sact;    /* 0x34 */
        uint32_t ci     = p->ci;      /* 0x38 */
        uint32_t sntf   = p->sntf;    /* 0x3C */
        uint32_t fbs    = p->fbs;     /* 0x40 */

        LOG_AHCI("-- Port %d --\n", i);
        LOG_AHCI("CLB=%08x CLBU=%08x  FB=%08x FBU=%08x\n", clb, clbu, fb, fbu);
        LOG_AHCI("IS =%08x  IE=%08x  CMD=%08x  RSV0=%08x\n", pis, pie, cmd, rsv0);
        LOG_AHCI("TFD=%08x  SIG=%08x  SSTS=%08x  SCTL=%08x\n", tfd, sig, ssts, sctl);
        LOG_AHCI("SERR=%08x  SACT=%08x  CI=%08x  SNTF=%08x  FBS=%08x\n",
                 serr, sact, ci, sntf, fbs);

        /* Reserved and vendor-specific dwords from your struct */
        for (int k = 0; k < 11; k += 4) {
            uint32_t a = p->rsv1[k + 0];
            uint32_t b = p->rsv1[k + 1];
            uint32_t c = p->rsv1[k + 2];
            uint32_t d = p->rsv1[k + 3];
            LOG_AHCI("RSV1[%02d..%02d]= %08x %08x %08x %08x\n",
                     k, k+3, a, b, c, d);
        }
        LOG_AHCI("VENDOR[0..3]= %08x %08x %08x %08x\n",
                 p->vendor[0], p->vendor[1], p->vendor[2], p->vendor[3]);
    }

    HBA_CMD_HEADER *hdr = (HBA_CMD_HEADER*)ahci_command_list_vaddr + slot;
    LOG_AHCI("PRDBC=%u (expect 512 on IDENTIFY)\n", hdr->prdbc);
}


void do_bringup() {
    assert(driver_status == DrvStatusBringup);

    switch (ahci_init_stage) {
    case 0:
        ahci_init_1();
        break;
    case 1:
        ahci_init_2();
        break;
    case 2:
        ahci_init_3();
        break;
    case 3:
        ahci_init_4();
        break;
    case 4:
        ahci_init_5();
        break;
    case 5:
        ahci_init_6();
        break;
    default:
        assert(false);
    }

    ahci_init_stage++;

    if (ahci_init_stage == 6) {
        driver_status = DrvStatusActive;
        LOG_AHCI("Handling any client requests while in initialisation...\n");
        handle_client(false);
    }
}

void notified(microkit_channel ch) {
   if (driver_status == DrvStatusBringup) { // add the unlikely compiler hint
        if (ch == timer_config.driver_id) {
            LOG_AHCI("notification from timer!\n");
            do_bringup();
        } else if (ch == 60) {
            LOG_AHCI("notification from device!\n");
            do_bringup();
            microkit_irq_ack(ch);
        } else {
            LOG_AHCI("notification on non-IRQ channel during bringup: %d\n", ch);
            // Is this in case the client messages us?
        }

        return;
    } /* else in inactive or active */

    if (ch == 60) { // Pick any channel
        LOG_AHCI("Got an irq from the device!\n");
        handle_client(true);
        microkit_irq_ack(ch);
    } else if (ch == blk_config.virt.id) {
        LOG_AHCI("Got a client request!\n");
        handle_client(false);
    } else if (ch == timer_config.driver_id) {
        LOG_AHCI("got impossible timer interrupt\n");
        assert(false);
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
    assert(device_resources.num_regions == 0);
    assert(device_resources.num_irqs == 0);

    LOG_AHCI("Beginning driver initialisation...\n");

    /* Setup the sDDF block queue */
    blk_queue_init(&blk_queue, blk_config.virt.req_queue.vaddr, blk_config.virt.resp_queue.vaddr,
                   blk_config.virt.num_buffers);

    pcie_init();

    assert(found_sata);

    print_pci_info(sata_bus, sata_device, sata_function, false);

    driver_status = DrvStatusBringup;
    do_bringup();
}

// TODO:    the design for this driver PD is that it needs to operate ALL of the 32 ports
//          we will have a seperate virt per port/device though
//          thus microkit_sdfgen will have to change so we can have multiple virts intead of just one.
