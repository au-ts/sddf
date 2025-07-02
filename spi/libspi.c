/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/spi/libspi.h>

#ifdef DEBUG_LIBSPI
#define LOG_LIBSPI(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_LIBSPI(...) do{}while(0)
#endif

#define PTR_TO_OFFSET(ptr) ((uintptr_t) (ptr - (void *) SPI_SLICE_REGION))

//TODO: update all commands javadocs
/**
 * Initialise libSPI and return the conf struct needed for all operations.
 */
int libspi_init(libspi_conf_t *conf_struct, spi_queue_handle_t *queue_handle)
{
    conf_struct->handle = queue_handle;

    // Allocate bitmask (i.e. zero portion of control region)
    sddf_memset(SPI_CONTROL_REGION, 0, LIBSPI_BITMASK_SZ);

    // Index commands after bytes used for bitmask
    conf_struct->control_start = (spi_cmd_t *) SPI_CONTROL_REGION + LIBSPI_BITMASK_SZ;
    return 0;
}

/**
 * Given configuration struct, return first available command from allocation bitmask.
 * Returns NULL if allocator is exhausted.
 */
static spi_cmd_t *__libspi_alloc_cmd(libspi_conf_t *conf, uint16_t len)
{
    // Find a contiguous range of free bits len long
    uint64_t start_idx = -1;
    uint64_t bit_idx;
    for (bit_idx = 0; bit_idx < LIBSPI_BITMASK_SZ * 8; bit_idx++) {
        bool occupied = (SPI_CONTROL_REGION[bit_idx / 8] & BIT(bit_idx % 8)) != 0;
        if (occupied) {
            start_idx = -1; 
        }
        // Start range of free bits
        else if (start_idx == -1) {
            start_idx = bit_idx;
            // Special case
            if (len == 1) {
                break;
            }
        }
        // End range of free bits
        else if (bit_idx - start_idx + 1 == len) {
            break;
        }
    }

    // No space
    if (start_idx == -1 || bit_idx - start_idx + 1 != len) {
        return NULL;
    }

    // Mark spaces as occupied
    for (uint16_t i = 0; i < len; i++) {
        SPI_CONTROL_REGION[(start_idx + i) / 8] |= BIT((start_idx + i) % 8);
    }

    return &conf->control_start[start_idx];  
}

/**
 * Given a pointer to a command in the control region, release this command to the allocator.
 */
static void __libspi_free_cmd(libspi_conf_t *conf, spi_cmd_t *cmd)
{
    // Make sure command is actually in the control region.
    assert((uintptr_t)cmd > (uintptr_t)SPI_CONTROL_REGION
           && ((uintptr_t)cmd - (uintptr_t)SPI_CONTROL_REGION) <= spi_config.control.size);

    size_t cmd_idx = cmd - conf->control_start;
    size_t bitmask_byte = cmd_idx / 8;
    uint8_t bitmask_bit = cmd_idx % 8;
    SPI_CONTROL_REGION[bitmask_byte] &= ~BIT(bitmask_bit);
}

// ########### SPI interface ###########

static inline int check_slice_buf(void *slice_buf)
{
    if ((uintptr_t)slice_buf < (uintptr_t)SPI_SLICE_REGION
        || (uintptr_t)slice_buf > ((uintptr_t)SPI_SLICE_REGION + spi_config.slice.size)) {
        LOG_LIBSPI_ERR("spi_write called with slice_buf not in slice region!");
        return -1;
    }
    return 0;
}

/**
 * Given a buffer pointer from the SLICE region, create an SPI op, dispatch and return when
 * complete. This is a blocking function call. Implements all single-cmd ops.
 * @return -1 if queue ops fail, positive value corresponding to spi_err_t, or 0 if successful.
 */
static int __spi_dispatch(libspi_conf_t *conf, spi_cs_line_t cs_line, spi_cmd_t *cmd,
    uint16_t cmd_len)
{
    spi_err_t error = 0;

    if (spi_enqueue_request(*conf->handle, cs_line, (uintptr_t)cmd, (uintptr_t)SPI_SLICE_REGION, 
            cmd_len)) {
        LOG_LIBSPI_ERR("__spi_dispatch failed to enqueue request!\n");
        error = -1;
        goto spi_dispatch_fail;
    }
    microkit_notify(spi_config.virt.id);

    // Await response.
    microkit_cothread_semaphore_wait(&async_io_semaphore);

    spi_cs_line_t returned_cs_line = 0;
    size_t err_cmd = 0;     // Irrelevant for single-command runs.
    if (spi_dequeue_response(*conf->handle, &returned_cs_line, &error, &err_cmd)) {
        LOG_LIBSPI_ERR("__spi_dispatch failed to dequeue response!\n");
        error = -1;
        goto spi_dispatch_fail;
    }
    assert(returned_cs_line == cs_line);   // If this ever fails, the protocol is broken or misused!
spi_dispatch_fail:
    for (uint16_t i = 0; i < cmd_len; i++) {
        __libspi_free_cmd(conf, &cmd[i]);
    }
    return error;
}

/**
 * Perform a simple SPI write given a SLICE region buffer containing data.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to spi_err_t, or 0 if successful.
 */
int spi_write(libspi_conf_t *conf, spi_cs_line_t cs_line, void *write_buf, uint16_t len)
{
    if (check_slice_buf(write_buf)) {
        return -1;
    }
 
    // Allocate a command
    spi_cmd_t *cmd = __libspi_alloc_cmd(conf, 1);
    if (cmd == NULL) {
        LOG_LIBSPI_ERR("spi_write failed to allocate command!\n");
        return -1;
    }

    cmd->read_offset = -1; 
    cmd->write_offset = PTR_TO_OFFSET(write_buf);
    cmd->len = len;
    cmd->mode = SPI_WRITE;

    return __spi_dispatch(conf, cs_line, cmd, 1); 
}

/**
 * Perform a simple SPI read given a SLICE region buffer to store result.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to spi_err_t, or 0 if successful.
 */
int spi_read(libspi_conf_t *conf, spi_cs_line_t cs_line, void *read_buf, uint16_t len)
{
    if (check_slice_buf(read_buf)) {
        return -1;
    }
 
    // Allocate a command
    spi_cmd_t *cmd = __libspi_alloc_cmd(conf, 1);
    if (cmd == NULL) {
        LOG_LIBSPI_ERR("spi_write failed to allocate command!\n");
        return -1;
    }

    cmd->read_offset = PTR_TO_OFFSET(read_buf);
    cmd->write_offset = -1; 
    cmd->len = len;
    cmd->mode = SPI_READ;

    return __spi_dispatch(conf, cs_line, cmd, 1);
}

/**
 * Perform an SPI read given a SLICE region buffer to store result, writing the cs_line of a
 * peripheral register first.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to spi_err_t, or 0 if successful.
 */
int spi_transfer(libspi_conf_t *conf, spi_cs_line_t cs_line, void *read_buf, void *write_buf,
    uint16_t len)
{
    if (check_slice_buf(read_buf) || check_slice_buf(write_buf)) {
        return -1;
    }
 
    // Allocate a command
    spi_cmd_t *cmd = __libspi_alloc_cmd(conf, 1);
    if (cmd == NULL) {
        LOG_LIBSPI_ERR("spi_write failed to allocate command!\n");
        return -1;
    }

    cmd->read_offset = PTR_TO_OFFSET(read_buf);
    cmd->write_offset = PTR_TO_OFFSET(read_buf);
    cmd->len = len;
    cmd->mode = SPI_TRANSFER;

    return __spi_dispatch(conf, cs_line, cmd, 1);
}

/**
 * Perform an SPI write then read; this is meant to mirror the access pattern of supplying a
 * some information then getting it, while the CS line remains low between them.
 * This is a blocking function call.
 * @return -1 if queue ops or command allocation fails, positive value corresponding to spi_err_t,
 *      or 0 if successful;
 */
int spi_writeread(libspi_conf_t *conf, spi_cs_line_t cs_line, void *read_buf, uint16_t read_len,
        void *write_buf, uint16_t write_len) {
    if (check_slice_buf(read_buf) || check_slice_buf(write_buf)) {
        return -1;
    }

    // Allocate 2 commands
    spi_cmd_t *cmds = __libspi_alloc_cmd(conf, 2);
    if (cmds == NULL) {
        LOG_LIBSPI_ERR("spi_writeread failed to allocate command!\n");
        return -1;
    }

    // Setup commands
    cmds[0].read_offset = -1;
    cmds[0].write_offset = PTR_TO_OFFSET(write_buf);
    cmds[0].len = write_len;
    cmds[0].mode = SPI_WRITE;

    cmds[1].read_offset = PTR_TO_OFFSET(read_buf);
    cmds[1].write_offset = -1;
    cmds[1].len = read_len;
    cmds[1].mode = SPI_READ;

    return __spi_dispatch(conf, cs_line, cmds, 2);
}

