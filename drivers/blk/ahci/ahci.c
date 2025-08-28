/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

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

static inline uint64_t min_u64(uint64_t a, uint64_t b) { return a < b ? a : b; }

#define DEBUG_DRIVER

#ifdef DEBUG_DRIVER
#define LOG_AHCI(...) do{ sddf_dprintf("AHCI |INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_AHCI(...) do{}while(0)
#endif
#define LOG_AHCI_ERR(...) do{ sddf_printf("AHCI |ERROR: "); sddf_printf(__VA_ARGS__); }while(0)

// MAKE SURE THESE MATCH meta.py (i dont think they have setvaddr in sdfgen)
const uint64_t ahci_command_list_paddr = 0x10000000;
const uint64_t ahci_command_list_vaddr = 0x720000000;
const uint64_t ahci_command_list_size = 0x8000;
const uint64_t ahci_FIS_paddr = 0x10008000;
const uint64_t ahci_FIS_vaddr = 0x720008000;
const uint64_t ahci_FIS_size = 0x2000;
const uint64_t ahci_command_tables_paddr = 0x10010000;
const uint64_t ahci_command_tables_vaddr = 0x720010000;
const uint64_t ahci_command_tables_size = 0x40000;
const uint64_t identify_command_paddr = 0x10050000;
const uint64_t identify_command_vaddr = 0x720050000;
const uint64_t identify_command_size = 0x4000;

// MAKE SURE THIS MATCH meta.py
#define DEVICE_IRQ_MICROKIT_CHANNEL 60

__attribute__((__section__(".device_resources"))) device_resources_t device_resources;
__attribute__((__section__(".blk_driver_config"))) blk_driver_config_t blk_config;
__attribute__((__section__(".timer_client_config"))) timer_client_config_t timer_config;

blk_queue_handle_t blk_queue;

/* Make sure to update drv_to_sddf_blk_status() as well */
// NOTE: command means a single hardware command however we use these to also describe the state of the overall request as well
typedef enum {
    RequestInit,
    RequestSuccess,
    RequestIrqWait,
    RequestError,
} request_status_t;

typedef enum {
    FIRST_STAGE,
    SECOND_STAGE,
    THIRD_STAGE,
    FOURTH_STAGE,
    FIFTH_STAGE,
    LAST_STAGE,
    COMPLETED_INITIALISATION,
} initialisation_stage_t;

/* The current action-status of the port */
typedef enum {
    PortStatusBringup,
    PortStatusInactive,
    PortStatusActive,
} port_status_t;

typedef enum {
    DriverStatusBringup,
    DriverStatusInactive,
    DriverStatusActive,
} driver_status_t;

typedef struct {
    port_status_t status;
    HBA_PORT* port_regs;
    ATA_IDENTIFY* identify_command;
    blk_storage_info_t *storage_info;

    struct {
        bool inflight;
        uint32_t id;
        blk_req_code_t code;
        int cmdslot;
        uintptr_t paddr;
        uint64_t blk_number;
        uint16_t blk_count;
        uint16_t success_count;
        request_status_t status;
    } blk_req;
} PortState;

static struct {
    bool dma64;
    HBA_MEM* hba_regs;
    driver_status_t status;
    PortState ports[32]; // Always do MAX (32)
    initialisation_stage_t init_stage;
    int number_of_command_slots;
} driver_state;

uint64_t sddf_blocks_to_ahci_blocks(int portno) {
    // Note: the clients must request a multiple of 4096 (BLK_TRANSFER_SIZE).
    // The multiple is what we set as the block size in storage_info.

    // NOTE: the sector size of the driver will always be <= block_size in storage info.
    // I.e. its not optimal for the sector size for the device to be 8192
    // But the clients request granularity is 4096

    // NOTE: we wont use ACHI driver outside of SATA land

    // For AHCI we only deal with 512, 1024, 2048, 4096, 8192 sector sizes
    blk_storage_info_t *storage_info = driver_state.ports[portno].storage_info;

    assert(((storage_info->block_size * BLK_TRANSFER_SIZE) % storage_info->sector_size) == 0);

    return (BLK_TRANSFER_SIZE * storage_info->block_size) / storage_info->sector_size;
}

uint64_t ahci_blocks_to_sddf_blocks(int port, uint64_t ahci_blocks) {
    blk_storage_info_t *storage_info = driver_state.ports[port].storage_info;

    assert(((storage_info->block_size * BLK_TRANSFER_SIZE) % storage_info->sector_size) == 0);

    uint64_t ahci_per_sddf = (BLK_TRANSFER_SIZE * storage_info->block_size) / storage_info->sector_size;

    assert(ahci_blocks % ahci_per_sddf == 0);
    return ahci_blocks / ahci_per_sddf;
}

static blk_resp_status_t request_to_sddf_blk_status(request_status_t status)
{
    switch (status) {
    case RequestSuccess:
        return BLK_RESP_OK;
    case RequestError:
        return BLK_RESP_ERR_UNSPEC;
    /* these should never make it to the block queue */
    case RequestIrqWait:
    case RequestInit:
    default:
        // We shoudn't get here
        assert(false);
        return 0xff;
    }
}

// Find a free command list slot
int find_cmdslot(HBA_PORT *port) {
    uint32_t slots = (port->sact | port->ci);

    for (int i = 0; i < driver_state.number_of_command_slots; i++) {
        if ((slots & 1) == 0)
            return i;
        slots >>= 1;
    }
    LOG_AHCI("Cannot find free command list entry\n");
    return -1;
}


// This read/writes "count" sectors from sector offset "start" to "buf" with LBA48 mode from HBA "port" determined via the portno.
// Calculations are done with bytes so that IDENTIFY commands can work with this funciton (we don't know sector size beforehand).
// Every PRDT entry contains 8K bytes (for convenience) data payload at most.
// Hardcode 8 prdt's max.
// Callers job to enable interrupts
// Start read/write command
// - Select an available command slot to use.
// - Setup command FIS.
// - Setup PRDT.
// - Setup command list entry.
// - Issue the command, and record separately that we have issued it.
bool ahci_send_command(int portno, uint64_t start, uint32_t count, uint64_t bytes, uint64_t buf, uint64_t command, bool read) {
    assert(count != 0);
    assert(bytes != 0);
    uint32_t startl = (uint32_t)(start & 0xFFFFFFFF);
    uint32_t starth = (uint32_t)((start >> 32) & 0xFFFF);
    assert(start >> 48 == 0);

    HBA_PORT *port = driver_state.ports[portno].port_regs;

    if (!driver_state.dma64) {
        if (buf > UINT32_MAX || buf + bytes - 1 > UINT32_MAX) {
            return false;
        }
    }

    // Clear pending/stale interrupt bits
    port->is = 0xFFFFFFFF;     // W1C
    port->serr = 0xFFFFFFFF;   // W1C

    int slot = find_cmdslot(port);
    if (slot == -1) {
        return false; // TODO: more specific error messages // or try again later
    }
    driver_state.ports[portno].blk_req.cmdslot = slot;

    LOG_AHCI("We are using cmdslot %d\n", slot);

    HBA_CMD_HEADER *cmdheader = (HBA_CMD_HEADER*)(ahci_command_list_vaddr + (portno << 10));
    cmdheader += slot;
    cmdheader->cfl = sizeof(FIS_REG_H2D)/sizeof(uint32_t);  // Command FIS size
    cmdheader->w = read ? 0 : 1;       // Read/write from device

    uint16_t prdtl = (uint16_t)((bytes + (8*1024 - 1)) >> 13); //
    if (prdtl == 0) {
        prdtl = 1;
    }
    if (prdtl > 8) {
        assert(false);
    }
    cmdheader->prdtl = prdtl;

    HBA_CMD_TBL *cmdtbl = (HBA_CMD_TBL*)(ahci_command_tables_vaddr + (portno << 13));
    cmdtbl += slot;
    sddf_memset(cmdtbl, 0, sizeof(HBA_CMD_TBL));

    uint64_t left = bytes;
    for (uint16_t i = 0; i < prdtl; i++) {
        uint32_t this_len = (left > 8*1024) ? (8*1024) : (uint32_t)left;

        cmdtbl->prdt_entry[i].dba  = (uint32_t)(buf & 0xFFFFFFFFu);
        cmdtbl->prdt_entry[i].dbau = (uint32_t)(buf >> 32);
        cmdtbl->prdt_entry[i].dbc  = this_len - 1;  // DBC = bytes - 1
        cmdtbl->prdt_entry[i].i    = 0;

        buf  += this_len;
        left -= this_len;
    }

    // Setup command
    FIS_REG_H2D *cmdfis = (FIS_REG_H2D*)(&cmdtbl->cfis);

    cmdfis->fis_type = FIS_TYPE_REG_H2D;
    cmdfis->c = 1;  // Command
    cmdfis->command = command;

    cmdfis->lba0 = (uint8_t)startl;
    cmdfis->lba1 = (uint8_t)(startl >>8);
    cmdfis->lba2 = (uint8_t)(startl >> 16);
    cmdfis->device = 1 << 6;  // LBA mode

    cmdfis->lba3 = (uint8_t)(startl >> 24);
    cmdfis->lba4 = (uint8_t)starth;
    cmdfis->lba5 = (uint8_t)(starth >> 8);

    cmdfis->countl = count & 0xFF;
    cmdfis->counth = (count >> 8) & 0xFF;

    // The below loop waits until the port is no longer busy before issuing a new command
    // Guarding against some last second weird shit happenibng (might not be necessary)
    // TODO: does linux do this?
    int spin = 0;
    while ((port->tfd & (ATA_DEV_BUSY | ATA_DEV_DRQ)) && spin < 1000000) {
        spin++;
    }
    if (spin == 1000000) {
        LOG_AHCI("Port is hung\n");
        return false; // TODO: more specific error messages // or try again later
    }

    port->ci = 1 << slot; // Issue command
    (void)port->ci;

    return true;
}

// This should continue looping through and sending the request

// Each time this gets called we issue another request and return irq wait

// Unless we are done or there is an error from the previous request in which we jsutr return the status

void ahci_do_request(int portno) {

    assert(driver_state.ports[portno].blk_req.status != RequestSuccess);
    assert(driver_state.ports[portno].blk_req.status != RequestError);

    HBA_PORT *port = driver_state.ports[portno].port_regs;

    if (driver_state.ports[portno].blk_req.status == RequestIrqWait) {
        // TFES
        if (port->is & (1u << 30)) {
            port->is = 0xFFFFFFFF;   // W1C clear
            driver_state.ports[portno].blk_req.status = RequestError;
            // TODO: this request is now done so i cant get anymore irqs or it breaks everythign
            return;
        }

        // Not done yet?
        if ((port->is & (1u << 0)) == 0) {
            port->is = 0xFFFFFFFF;   // W1C clear
            driver_state.ports[portno].blk_req.status = RequestError;
            // TODO: this request is now done so i cant get anymore irqs or it breaks everythign
            return;

        }

        // FIS arrived; make sure our slot’s CI bit is now cleared
        if (driver_state.ports[portno].blk_req.cmdslot >= 0 && (port->ci & (1u << driver_state.ports[portno].blk_req.cmdslot)) != 0) {
            port->is = 0xFFFFFFFF;   // W1C clear
            driver_state.ports[portno].blk_req.status = RequestError;
            // TODO: this request is now done so i cant get anymore irqs or it breaks everythign
            return; // IS THIS correct
        }

        // Ack the completion we handled
        port->is = 0xFFFFFFFF;   // W1C clear

        LOG_AHCI("command complete (IRQ)\n");

        // Reverse engineer how much we sent

        uint64_t max_transfer = ahci_blocks_to_sddf_blocks(portno, 128);
        uint64_t total_left = driver_state.ports[portno].blk_req.blk_count - driver_state.ports[portno].blk_req.success_count;

        driver_state.ports[portno].blk_req.success_count += min_u64(max_transfer, total_left);
        driver_state.ports[portno].blk_req.cmdslot = -1;

    } else if (driver_state.ports[portno].blk_req.status != RequestInit) {
        assert(false);
    }


    // Send the rest of the request
    if (driver_state.ports[portno].blk_req.blk_count == driver_state.ports[portno].blk_req.success_count) {
        driver_state.ports[portno].blk_req.status = RequestSuccess;
        return;
    } else if (driver_state.ports[portno].blk_req.blk_count < driver_state.ports[portno].blk_req.success_count) {
        assert(false);
    }

    bool read;
    uint64_t command;
    if (driver_state.ports[portno].blk_req.code == BLK_REQ_READ) {
        read = true;
        command = ATA_CMD_READ_DMA_EX;
    } else if (driver_state.ports[portno].blk_req.code == BLK_REQ_WRITE) {
        read = false;
        command = ATA_CMD_WRITE_DMA_EX;
    } else {
        assert(false);
    }

    // Figure out how much to send (one command chunk)

    uint32_t bps = driver_state.ports[portno].storage_info->sector_size;  // bytes per sector

    // sDDF blocks -> AHCI sectors
    uint64_t sector_conversion     = sddf_blocks_to_ahci_blocks(portno);
    uint64_t sector_start          = driver_state.ports[portno].blk_req.blk_number  * sector_conversion;
    uint64_t sector_count_total    = driver_state.ports[portno].blk_req.blk_count   * sector_conversion;
    uint64_t sector_count_done     = driver_state.ports[portno].blk_req.success_count * sector_conversion;
    uint64_t sector_count_remaining= sector_count_total - sector_count_done;

    // With 8 PRDTs * 8 KiB = 64 KiB max per command:
    const uint32_t MAX_CMD_BYTES      = 8u * 8u * 1024u;          // 64 KiB
    uint32_t       max_sectors_per_cmd = MAX_CMD_BYTES / bps;     // e.g., 128 if bps=512, 16 if bps=4096

    // Sanity: sector_size should divide 64 KiB (true for 512/1K/2K/4K/8K)
    assert(max_sectors_per_cmd > 0);

    // Sectors to issue in this command (cap by remaining and per-cmd max)
    uint32_t count = (sector_count_remaining < max_sectors_per_cmd)
                   ? (uint32_t)sector_count_remaining
                   : max_sectors_per_cmd;

    // Bytes to transfer this command
    uint64_t bytes = (uint64_t)count * (uint64_t)bps;

    // Byte offset into client buffer
    uint64_t buf = driver_state.ports[portno].blk_req.paddr + (sector_count_done * (uint64_t)bps);

    // 32-bit DMA guard (inclusive end) if HBA doesn't support 64-bit DMA
    if (!driver_state.dma64) {
        if (buf > UINT32_MAX || (buf + bytes - 1) > UINT32_MAX) {
            driver_state.ports[portno].blk_req.status = RequestError;
            return;
        }
    }

    // Issue the command: start LBA is in sectors; COUNT in sectors; PRDT built from 'bytes'
    bool res = ahci_send_command(
        portno,
        /*start*/  sector_start + sector_count_done,
        /*count*/  count,
        /*bytes*/  bytes,
        /*buf*/    buf,
        /*command*/command,
        /*read*/   read
    );
    if (!res) {
        driver_state.ports[portno].blk_req.status = RequestError;
        return;
    }

    driver_state.ports[portno].blk_req.status = RequestIrqWait;
}

void handle_client(bool was_irq, int portno) {
    LOG_AHCI("Who calls this %d\n", portno);
    assert(portno == 0); // TODO: we only handle one port for now

    if (was_irq == false) {
        if (driver_state.ports[portno].blk_req.inflight) {
            /* Only handle block queue notifications when idle */
            return;
        }

        int err = blk_dequeue_req(&blk_queue, &driver_state.ports[portno].blk_req.code, &driver_state.ports[portno].blk_req.paddr,
                                      &driver_state.ports[portno].blk_req.blk_number, &driver_state.ports[portno].blk_req.blk_count,
                                      &driver_state.ports[portno].blk_req.id);

        if (err == -1) {
            /* no client requests; we likely handled it already.
               this can happen as we can dequeue outstanding requests following an
               IRQ being handled, which might happen before we get the virtualiser
               notification from the microkit event loop. */
            return;
        }

        driver_state.ports[portno].blk_req.inflight = true;
        driver_state.ports[portno].blk_req.success_count = 0;
        driver_state.ports[portno].blk_req.status = RequestInit;

        LOG_AHCI("Received command: code=%d, paddr=0x%lx, block_number=%lu, count=%d, id=%d\n",
                       driver_state.ports[portno].blk_req.code, driver_state.ports[portno].blk_req.paddr, driver_state.ports[portno].blk_req.blk_number,
                       driver_state.ports[portno].blk_req.blk_count, driver_state.ports[portno].blk_req.id);

    }

    /* Should never get IRQs without inflight requests */
    if (!driver_state.ports[portno].blk_req.inflight) {
        assert(false);
    }

    blk_resp_status_t response_status;

    switch (driver_state.ports[portno].blk_req.code) {
    case BLK_REQ_FLUSH:
    case BLK_REQ_BARRIER: {
        /* No-ops. Because we only do 1 request at a time | what are the proper semantics? */
        response_status = BLK_RESP_OK;
        driver_state.ports[portno].blk_req.success_count = 0;
        break;
    }

    case BLK_REQ_READ:
    case BLK_REQ_WRITE: {
        // we only process one client request and serialise it chunk by chunk over 1 port
        ahci_do_request(portno);

        if (driver_state.ports[portno].blk_req.status == RequestIrqWait) {
            return;
        } else if (driver_state.ports[portno].blk_req.status == RequestError) {
            // TODO: retry or return error to client or even reset the port
            // TODO: make the reponse status better
        }

        response_status = request_to_sddf_blk_status(driver_state.ports[portno].blk_req.status);
        break;
    }

    default: {
        response_status = BLK_RESP_ERR_INVALID_PARAM;
        break;
    }
    }

    int err = blk_enqueue_resp(&blk_queue, response_status, driver_state.ports[portno].blk_req.success_count, driver_state.ports[portno].blk_req.id);
    assert(!err);
    LOG_AHCI("Enqueued response: status=%d, success_count=%d, id=%d\n", response_status, driver_state.ports[portno].blk_req.success_count,
               driver_state.ports[portno].blk_req.id);
    microkit_notify(blk_config.virt.id);

    driver_state.ports[portno].blk_req.inflight = false;

    /* Tail-call to handle another request */
    return handle_client(false, portno);
}

// We just enable:
// - DHRS: Register D2H FIS on command completion (non-NCQ).
// - TFES: Always catch errors.
void enable_irqs_for_ports() {
    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            HBA_PORT *port = driver_state.ports[i].port_regs;
            port->is = 0xFFFFFFFF; // W1C
            (void)port->is;
            port->ie = (1u<<0) | (1u<<30); // DHRS + TFES
        }
    }
}

void ahci_copy_serial(char dst[BLK_MAX_SERIAL_NUMBER + 1], ATA_IDENTIFY *id) {
    volatile uint16_t *w = id->serial_number_words;
    size_t cap = BLK_MAX_SERIAL_NUMBER;
    size_t out = 0;
    for (int k = 0; k < 10 && out < cap; k++) {
        uint16_t v = w[k];            // volatile read once
        char hi = (char)(v >> 8);     // ATA strings are byte-swapped per word
        char lo = (char)(v & 0xFF);
        if (out < cap) dst[out++] = hi;
        if (out < cap) dst[out++] = lo;
    }
    while (out > 0 && dst[out - 1] == ' ') out--;
    dst[out] = '\0';
}

bool ahci_identify_device(int portno) {
    return ahci_send_command(portno, 0 /* start */, 1 /* 1 sector */, 512 /* bytes */, identify_command_paddr + (portno << 9), 0xEC, /* IDENTIFY command */ true /* read */);
}

bool check_identify_device_response(int portno) {
    HBA_PORT *port = driver_state.ports[portno].port_regs;

    if (port->is & (1u << 30)) {
        LOG_AHCI("Write disk error\n");
        // We dont clear is or serr because we this port is now inactive
        return false;
    }

    const uint32_t done = (1u << 0) | (1u << 1) | (1u << 3); // DHRS|PSS|SDBS // on the vb105 it was the PSS one that signalled completion
    if ((port->is & done) == 0) {
        // We dont clear is or serr because we this port is now inactive
        return false;
    }

    int slot = driver_state.ports[portno].blk_req.cmdslot;
    if (slot >= 0 && (port->ci & (1u << slot)) != 0) {
        // We dont clear is or serr because we this port is now inactive
        return false;
    }

    port->is = 0xFFFFFFFF; // W1C
    port->serr = 0xFFFFFFFF; // W1C
    (void)port->is;

    return true;
}

void setup_ports_blk_storage_info_1() {
    // So much easier if we just use a timeout to get them instead of irqs.
    LOG_AHCI("Send IDENTIFY ATA command to connected drives. Get their sector size and count...\n");
    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup && !ahci_identify_device(i)) {
            driver_state.ports[i].status = PortStatusInactive;
        }
    }

    sddf_timer_set_timeout(timer_config.driver_id, 1 * NS_IN_S); // plenty of time
}

void setup_ports_blk_storage_info_2() {
    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            // check if we got a response
            if (!check_identify_device_response(i) || i != 0) { // we only support 1 virt which is for port 0
                driver_state.ports[i].status = PortStatusInactive;
            } else {
                // TODO: we currently just assume this virt is for port0
                driver_state.ports[i].storage_info = blk_config.virt.storage_info.vaddr;
                blk_storage_info_t *storage_info = driver_state.ports[i].storage_info;
                assert(!storage_info->ready);

                // Data is ready in PRDT buffer
                ATA_IDENTIFY *identify_command = (ATA_IDENTIFY *)(identify_command_vaddr + (i << 9));
                driver_state.ports[i].identify_command = identify_command;

                // We only support 48bit LBA, i.e. basically all devices post 2003
                if (!(identify_command->feature_support_83 & (1 << 10))) {
                    driver_state.ports[i].status = PortStatusInactive;
                    continue;
                }

                ahci_copy_serial(storage_info->serial_number, identify_command);

                if (identify_command->sector_size_flags_106 & (1 << 12)) {
                    storage_info->sector_size =
                        identify_command->logical_sector_size_lo |
                        (identify_command->logical_sector_size_hi << 16);
                } else {
                    storage_info->sector_size = 512; // default
                }

                storage_info->block_size = 1; // TODO
                storage_info->queue_depth = 1; // NCQ currently not implemented
                storage_info->read_only = false; // TODO

                if (((storage_info->block_size * BLK_TRANSFER_SIZE) % storage_info->sector_size) != 0) {
                    // See sddf_blocks_to_ahci_blocks()
                    driver_state.ports[i].status = PortStatusInactive;
                    continue;
                }

                // Geometry (legacy CHS)
                storage_info->cylinders = identify_command->legacy_logical_cylinders_1;
                storage_info->heads     = identify_command->legacy_logical_heads_3;
                storage_info->blocks    = identify_command->legacy_sectors_per_track_6;

                uint64_t sectors =  ((uint64_t)identify_command->lba48_sectors_3 << 48) |
                                    ((uint64_t)identify_command->lba48_sectors_2 << 32) |
                                    ((uint64_t)identify_command->lba48_sectors_1 << 16) |
                                    (uint64_t)identify_command->lba48_sectors_0;

                storage_info->capacity = sectors * storage_info->sector_size / BLK_TRANSFER_SIZE;
                LOG_AHCI("Drive size (blocks): %lu at port %d\n", storage_info->capacity, i);
                blk_storage_set_ready(storage_info, true); // TODO: we only do this for devices that make it this far.
            }
        }
    }
}

// Start command engine
void start_cmd(HBA_PORT *port) {
    LOG_AHCI("Starting command engine...\n");

    // 1. Wait until CR (command engine running) is cleared
    while (port->cmd & HBA_PxCMD_CR) {}

    // 2. Enable FIS receive
    port->cmd |= HBA_PxCMD_FRE;

    // 3. Wait until FR (FIS receive running) is set // TODO: poll forever
    while (!(port->cmd & HBA_PxCMD_FR)) {}

    // 4. Start command engine
    port->cmd |= HBA_PxCMD_ST;

    // 5. Verify CR is set
    while (!(port->cmd & HBA_PxCMD_CR)) {} // TODO: poll forever

    LOG_AHCI("Successfully started\n");
}

// Stop command engine
void stop_cmd(HBA_PORT *port) {
    LOG_AHCI("Stopping command engine...\n");

    // 1. Clear ST (stop command list engine)
    port->cmd &= ~HBA_PxCMD_ST;

    // 2. Wait until CR (bit15) is cleared
    while (port->cmd & HBA_PxCMD_CR) {} // TODO: poll forever

    // 3. Clear FRE (stop FIS receive)
    port->cmd &= ~HBA_PxCMD_FRE;

    // 4. Wait until FR (bit14) is cleared
    while (port->cmd & HBA_PxCMD_FR) {} // TODO: poll forever

    LOG_AHCI("Successfully stopped\n");
}

/* For now we leave enough space for best case scenario where all 32 ports are implemented. */
void ports_rebase() {
    LOG_AHCI("Checking alignment of DMA addresses\n");
    assert((ahci_command_list_paddr & (1024 - 1)) == 0);  // CLB: 1 KiB
    assert((ahci_FIS_paddr          & (256  - 1)) == 0);  // FB : 256 B
    assert((ahci_command_tables_paddr & (256 - 1)) == 0); // CT : 256 B

    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            HBA_PORT *port = driver_state.ports[i].port_regs;

            stop_cmd(port); // Stop command engine

            // Command list entry size = 32
            // Command list entry max count = 32
            // Command list max size = 32 * 32 = 1K per port
            port->clb  = (uint32_t)((ahci_command_list_paddr + (i << 10)) & 0xFFFFFFFF);
            port->clbu = (uint32_t)((ahci_command_list_paddr + (i << 10)) >> 32);
            sddf_memset((void*)(ahci_command_list_vaddr + (i << 10)), 0, 1024);

            // FIS entry size = 256 bytes per port
            port->fb = (uint32_t)((ahci_FIS_paddr  + (i << 8)) & 0xFFFFFFFF);
            port->fbu = (uint32_t)((ahci_FIS_paddr + (i << 8)) >> 32);
            sddf_memset((void*)(ahci_FIS_vaddr + (i << 8)), 0, 256);

            // Command table size = 256 * 32 = 8K per port
            HBA_CMD_HEADER *cmdheader = (HBA_CMD_HEADER*)(ahci_command_list_vaddr + (i << 10));
            for (int j = 0; j < 32; j++) {
                cmdheader[j].prdtl = 8; // @Tristan: I'm deciding 8 prdt entries per command table
                // 256 bytes per command table, 64 + 16 + 48 + (16 * 8)

                cmdheader[j].ctba = (uint32_t)((ahci_command_tables_paddr + (i << 13) + (j << 8)) & 0xFFFFFFFF);
                cmdheader[j].ctbau = (uint32_t)((ahci_command_tables_paddr + (i << 13) + (j << 8)) >> 32);
                sddf_memset((void*)(ahci_command_tables_vaddr + (i << 13) + (j << 8)), 0, 256);
            }

            start_cmd(port); // Start command engine
        }
    }
}

int check_type(HBA_PORT *port) {
    uint32_t ssts = port->ssts;

    uint8_t ipm = (ssts >> 8) & 0x0F;
    uint8_t det = ssts & 0x0F;

    if (det != HBA_PORT_DET_PRESENT) {
        return AHCI_DEV_NULL;
    }
    if (ipm != HBA_PORT_IPM_ACTIVE) {
        return AHCI_DEV_NULL;
    }

    switch (port->sig) {
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

void probe_ports() {
    bool one_drive_found = false;

    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            int dt = check_type(driver_state.ports[i].port_regs);

            if (dt == AHCI_DEV_SATA) {
                LOG_AHCI("SATA drive found at port %d\n", i);
                one_drive_found = true;
            } else if (dt == AHCI_DEV_SATAPI) {
                LOG_AHCI("SATAPI drive found at port %d. Currently NO Support!\n", i);
                driver_state.ports[i].status = PortStatusInactive;
            } else if (dt == AHCI_DEV_SEMB) {
                LOG_AHCI("SEMB drive found at port %d. Currently NO Support!\n", i);
                driver_state.ports[i].status = PortStatusInactive;
            } else if (dt == AHCI_DEV_PM) {
                LOG_AHCI("PM drive found at port %d. Currently NO Support!\n", i);
                driver_state.ports[i].status = PortStatusInactive;
            } else {
                LOG_AHCI("No drive found at port %d\n", i);
                driver_state.ports[i].status = PortStatusInactive;
            }
        }
    }

    if (!one_drive_found) {
        // TODO: @Tristan: for now something definitely has gone wrong if theres no SATA drives found.
        LOG_AHCI("No SATA drives found at all \n");
        assert(false);
    }
}

void ports_reset_1() {
    // Engine must be stopped before we touch SCTL
    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            HBA_PORT *port = driver_state.ports[i].port_regs;

            stop_cmd(port); // Stop command engine

            // Clear all the interrupts
            port->ie = 0;
            (void)port->ie;

            port->is   = 0xFFFFFFFF; // W1C
            port->serr = 0xFFFFFFFF; // W1C

            port->cmd |= (1u << 1); // spin-up disk if needed

            // COMRESET
            port->sctl = (port->sctl & ~0xF) | 0x1; // DET=1
        }
    }

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_MS);
}

void ports_reset_2() {
    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            HBA_PORT *port = driver_state.ports[i].port_regs;

            port->sctl &= ~0xF; // DET=0
        }
    }

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void ports_reset_3() {
    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusBringup) {
            HBA_PORT *port = driver_state.ports[i].port_regs;

            if (((port->ssts & 0xF) != HBA_PORT_DET_PRESENT) ||
                   (((port->ssts >> 8) & 0xF) != HBA_PORT_IPM_ACTIVE)) {
                LOG_AHCI("Something went wrong initialising port %d\n", i);
                driver_state.ports[i].status = PortStatusInactive;
            }

            // Clear all the interrupts
            port->ie = 0;
            (void)port->ie;

            port->is   = 0xFFFFFFFF; // W1C
            port->serr = 0xFFFFFFFF; // W1C
        }
    }
}

void initialise_implemented_ports() {
    uint32_t pi = driver_state.hba_regs->pi;
    for (int i = 0; i < 32; i++) {
        if (pi & 1) {
            driver_state.ports[i].port_regs = &driver_state.hba_regs->ports[i];
            driver_state.ports[i].status = PortStatusBringup;
        } else {
            driver_state.ports[i].port_regs = NULL;
            driver_state.ports[i].status = PortStatusInactive;
        }
        pi >>= 1;
    }
}

void ahci_get_num_cmd_slots() {
    // This field says how many command slots each port supports (minus one).
    driver_state.number_of_command_slots = ((driver_state.hba_regs->cap >> 8) & 0x1Fu) + 1;
    LOG_AHCI("Number of command slots is %u\n", driver_state.number_of_command_slots);
}

void validate_allocated_dma_paddr() {
    driver_state.dma64 = driver_state.hba_regs->cap & (1 << 31);
    if (!driver_state.dma64) {
        assert(ahci_command_tables_paddr <= UINT32_MAX);
        assert(ahci_FIS_paddr <= UINT32_MAX);
        assert(ahci_command_list_paddr <= UINT32_MAX);

        assert(ahci_command_tables_paddr + ahci_command_tables_size - 1 <= UINT32_MAX);
        assert(ahci_FIS_paddr + ahci_FIS_size - 1 <= UINT32_MAX);
        assert(ahci_command_list_paddr + ahci_command_list_size - 1 <= UINT32_MAX);
    }
}

void ahci_hba_reset_1() {
    LOG_AHCI("Issuing Host Bus Adapter (HBA) reset...\n");
    driver_state.hba_regs->ghc |= 1u;
    (void)driver_state.hba_regs->ghc;

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void ahci_hba_reset_2() {
    if (driver_state.hba_regs->ghc & 1u) {
        LOG_AHCI("Reset hasn't been complete, for now we fail but we could do everything manually...\n");
        assert(false);
        // Could also just set the driver as inactive
    }

    LOG_AHCI("HBA reset complete\n");
}

void ahci_boh_procedure_1() {
    if ((driver_state.hba_regs->cap2 & 1u) == 0) {
        LOG_AHCI("BOH not supported, skipping handoff\n");
        // To help with control flow we just do timeout still
    } else if ((driver_state.hba_regs->bohc & 1u) == 0) {
        LOG_AHCI("BIOS not owning controller, no handoff needed\n");
        // To help with control flow we just do timeout still
    } else {
        LOG_AHCI("Requesting OS ownership...\n");
        driver_state.hba_regs->bohc |= (1u << 1);
        // BIOS firmware should now, Clear BOS to 0 (releasing ownership).
    }

    sddf_timer_set_timeout(timer_config.driver_id, NS_IN_S);
}

void ahci_boh_procedure_2() {
    if ((driver_state.hba_regs->bohc & 1u) != 0) {
        LOG_AHCI("BIOS still hasn't released!\n");
        LOG_AHCI("Proceed anyway; some firmwares ignore BOS or release implictly when we HBA reset\n");
        // TODO: Revisit as we might have to disable in the firmware? Or set the driver as inactive
    }

    // Clear any semaphore-change latched status
    driver_state.hba_regs->bohc = (1u << 2);

    LOG_AHCI("BIOS/OS handoff complete (BOS=%u, OS=%u)\n",
             !!(driver_state.hba_regs->bohc & 1u), !!(driver_state.hba_regs->bohc & (1u << 1)));
}

void ahci_init_1() {
    LOG_AHCI("== Starting AHCI initialisation (1)...\n");

    driver_state.hba_regs = (HBA_MEM*)ahci_abar_vaddr;

    LOG_AHCI("Doing BIOS/OS handoff proceedure...\n");
    ahci_boh_procedure_1();
}

void ahci_init_2() {
    LOG_AHCI("== Continuing AHCI initialisation (2)...\n");

    LOG_AHCI("Continuing BIOS/OS handoff proceedure...\n");
    ahci_boh_procedure_2();

    LOG_AHCI("Resetting controller...\n");
    ahci_hba_reset_1();
}

void ahci_init_3() {
    LOG_AHCI("== Continuing AHCI initialisation (3)...\n");

    LOG_AHCI("Continuing resetting controller...\n");
    ahci_hba_reset_2();

    LOG_AHCI("Enabling AHCI mode...\n");
    driver_state.hba_regs->ghc |= (1u << 31);
    (void)driver_state.hba_regs->ghc;

    LOG_AHCI("Checking if physical addresses for data structures are valid for DMA...\n");
    validate_allocated_dma_paddr();

    LOG_AHCI("Checking the number of command slots/headers...\n");
    ahci_get_num_cmd_slots();

    LOG_AHCI("Initialise implemented ports...\n");
    initialise_implemented_ports();

    LOG_AHCI("Resetting all ports...\n");
    ports_reset_1();
}

void ahci_init_4() {
    LOG_AHCI("== Continuing AHCI initialisation (4)...\n");

    LOG_AHCI("Continuing resetting all ports...\n");
    ports_reset_2();
}

void ahci_init_5() {
    LOG_AHCI("== Continuing AHCI initialisation (5)...\n");

    LOG_AHCI("Continuing resetting all ports...\n");
    ports_reset_3();

    LOG_AHCI("Detecting attached SATA devices...\n");
    probe_ports();

    LOG_AHCI("AHCI port memory space initialisation...\n");
    ports_rebase();

    LOG_AHCI("Setting up blk storage info for the ports...\n");
    setup_ports_blk_storage_info_1();
}

void ahci_init_6() {
    LOG_AHCI("== Continuing AHCI initialisation (6)...\n");

    LOG_AHCI("Continuing setting up blk storage info for the ports...\n");
    setup_ports_blk_storage_info_2();

    LOG_AHCI("Enabling interrupts in HBA...\n");
    driver_state.hba_regs->ghc |= (1u << 1);

    LOG_AHCI("Enabling interrupts for ports ...\n");
    enable_irqs_for_ports();

    LOG_AHCI("Driver initialisation complete\n");
}

static const char* port_status_str(port_status_t s) {
    switch (s) {
        case PortStatusBringup: return "Bringup";
        case PortStatusInactive: return "Inactive";
        case PortStatusActive: return "Active";
        default: return "Unknown";
    }
}

void dump_ahci_registers(bool only_non_inactive) {
    HBA_MEM *hba = driver_state.hba_regs;
    if (!hba) {
        LOG_AHCI("dump_ahci_registers: driver_state.hba_regs is NULL\n");
        return;
    }

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

    LOG_AHCI("=== Per-Port Reg Dump (implemented mask PI=0x%08x) ===\n", pi);

    for (int i = 0; i < 32; i++) {
        if (!(pi & (1u << i))) {
            continue;
        }

        if (only_non_inactive &&
            driver_state.ports[i].status == PortStatusInactive) {
            continue;
        }

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

        LOG_AHCI("-- Port %d (PortState=%s) --\n",
                 i, port_status_str(driver_state.ports[i].status));
        LOG_AHCI("CLB=%08x CLBU=%08x  FB=%08x FBU=%08x\n", clb, clbu, fb, fbu);
        LOG_AHCI("IS =%08x  IE=%08x  CMD=%08x  RSV0=%08x\n", pis, pie, cmd, rsv0);
        LOG_AHCI("TFD=%08x  SIG=%08x  SSTS=%08x  SCTL=%08x\n", tfd, sig, ssts, sctl);
        LOG_AHCI("SERR=%08x  SACT=%08x  CI=%08x  SNTF=%08x  FBS=%08x\n",
                 serr, sact, ci, sntf, fbs);
    }
}

/*
IRQ Handler Checklist:
    1. Check global interrupt status. Write back its value. For all the ports that have a corresponding set bit...
    2. Check the port interrupt status. Write back its value. If zero, continue to the next port.
    3. If error bit set, reset port/retry commands as necessary.
    4. Compare issued commands register to the commands you have recorded as issuing.
        For any bits where a command was issued but is no longer running, this means that the command has completed.
    5. Once done, continue checking if any other devices sharing the IRQ also need servicing.
*/
void irq_handler() {
    assert(driver_state.status == DriverStatusActive);

    if (driver_state.hba_regs->is == 0) {
        return;
    }

    uint32_t clear_mask = 0;

    for (int i = 0; i < 32; i++) {
        if (driver_state.ports[i].status == PortStatusActive && (driver_state.hba_regs->is & (1 << i))) {
            // service interrupt on this port which MUST be a response to command
            LOG_AHCI("Handling irq from port %d\n", i);
            handle_client(true, i);
            clear_mask |= (1 << i);
        } else if (driver_state.hba_regs->is & (1 << i)) {
            // we should not have gotten an interrupt here
            assert(false);
        }
    }

    driver_state.hba_regs->is = clear_mask; // W1C
    (void)driver_state.hba_regs->is;
}

void ahci_init() {
    assert(driver_state.status == DriverStatusBringup);

    switch (driver_state.init_stage) {
    case FIRST_STAGE:
        ahci_init_1();
        // timeout started
        break;
    case SECOND_STAGE:
        ahci_init_2();
        // timeout started
        break;
    case THIRD_STAGE:
        ahci_init_3();
        // timeout started
        break;
    case FOURTH_STAGE:
        ahci_init_4();
        // timeout started
        break;
    case FIFTH_STAGE:
        ahci_init_5();
        // timeout started
        break;
    case LAST_STAGE:
        ahci_init_6();
        break;
    default:
        assert(false);
    }

    driver_state.init_stage++;

    if (driver_state.init_stage == COMPLETED_INITIALISATION) {
        for (int i = 0; i < 32; i++) {
            if (driver_state.ports[i].status == PortStatusBringup) {
                driver_state.ports[i].status = PortStatusActive;
            }
        }

        driver_state.status = DriverStatusActive;
        LOG_AHCI("Handling any client requests while in initialisation...\n");
        for (int i = 0; i < 32; i++) {
             if (driver_state.ports[i].status == PortStatusActive) {
                handle_client(false, i);
            }
        }
    }
}

void notified(microkit_channel ch) {
    if (driver_state.status == DriverStatusBringup) { // TODO: should add the unlikely compiler hint
        if (ch == timer_config.driver_id) {
            LOG_AHCI("notification from timer!\n");
            ahci_init();
        } else if (ch == DEVICE_IRQ_MICROKIT_CHANNEL) {
            LOG_AHCI("notification from device ... ignoring\n");
            microkit_irq_ack(ch);
        } else {
            LOG_AHCI("notification on non-IRQ channel during bringup: %d\n", ch);
        }

        return;
    } /* else in inactive or active */

    if (ch == DEVICE_IRQ_MICROKIT_CHANNEL) {
        LOG_AHCI("Got an irq from the device!\n");
        irq_handler();
        microkit_irq_ack(ch);
    } else if (ch == blk_config.virt.id) {
        LOG_AHCI("Got a client request!\n");
        handle_client(false, 0); // TODO: dont hardcode the port
    } else if (ch == timer_config.driver_id) {
        LOG_AHCI("got impossible timer interrupt\n");
        assert(false);
    } else {
        LOG_AHCI("notification on unknown channel: %d\n", ch);
        assert(false);
    }
}

/*
Initialisation Checklist:
    1. Enable interrupts, DMA, and memory space access in the PCI command register
    2. Memory map BAR 5
    3. Perform BIOS/OS handoff (if the bit in the extended capabilities is set)
    4. Reset the controller
    5. Register IRQ handler, using interrupt line given in the PCI register.
        This interrupt line may be shared with other devices, so the usual implications of this apply.
        NOTE: this is for legacy ISA/PIC IRQ not APIC/ACPI.
    6. Enable AHCI mode and interrupts in global host control register.
    7. Read capabilities registers. Check 64-bit DMA is supported if you need it.

    For all the implemented ports:
        1. Allocate physical memory for its command list, the received FIS, and its command tables.
            Make sure the command tables are 128 byte aligned. Memory map these as uncacheable.
        2. Stop the port
        3. Reset the port.
        4. Read signature/status of the port to see if it connected to a drive.
        5. Set command list and received FIS address registers (and upper registers, if supported).
        6. Setup command list entries to point to the corresponding command table.
        7. Start command list processing with the port's command register.
        8. Send IDENTIFY ATA command to connected drives. Get their sector size and count.
        9. Enable interrupts for the port. The D2H bit will signal completed commands. Too complicated to be irq driven here.
        10. Now we can process client requests for this port.
*/

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

    assert(found_sata_controller);

    driver_state.status = DriverStatusBringup;
    driver_state.init_stage = FIRST_STAGE;
    ahci_init();
}

/*
    TODO's
    - change i variable to portno.
    - fix the timeouts lengths.
    - add more specific error messages for request.
    - add retries or port resets?
    - check where we assert, we probably want more graceful handling.
    - think more about irq control flow, i think the device can do some weird things.
*/
