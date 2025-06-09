/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/i2c/libi2c.h>

#ifdef DEBUG_LIBI2C
#define LOG_LIBI2C(...) do{ sddf_dprintf("CLIENT|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_LIBI2C(...) do{}while(0)
#endif

/**
 * Initialise libI2C and return the conf struct needed for all operations.
 */
int libi2c_init(libi2c_conf_t *conf_struct, i2c_queue_handle_t *queue_handle)
{
    conf_struct->handle = queue_handle;

    // Allocate bitmask (i.e. zero portion of data region)
    for (int i = 0; i < LIBI2C_BITMASK_SZ; i++) {
        I2C_DATA_REGION[i] = 0;
    }

    // Index commands after bytes used for bitmask
    conf_struct->data_start = (void *)(I2C_DATA_REGION + LIBI2C_BITMASK_SZ);
    return 0;
}

// ########### Command allocator functions ############
// SDFgen will do a lot of the work for us, but unfortunately all of the variables it generates
// are considered runtime-context by the C compiler. As a result, we need to do some magic to
// have a sane allocator which doesn't need a bunch of #defines set based on region sizes.
//
// This allocator sets aside a tracking bitmask from the available room in the data region.
// Commands are 2 bytes, hence a region of size S can store a max of S/2 commands.
// S/2 commands can be indexed using (S/2)/64 = S/128. We set aside this many bitmask words at
// the base of the region. The remaining C=S - (S/128)=127/128 * S bytes are used to store
// ((127/128)S) / 2 commands.

/**
 * Given configuration struct, return first available command from allocation bitmask.
 * Returns NULL if allocator is exhausted.
 */
static i2c_cmd_t *__libi2c_alloc_cmd(libi2c_conf_t *conf)
{
    // Find first non-zero byte in bitmask range
    for (int i = 0; i < LIBI2C_BITMASK_SZ; i++) {
        uint8_t mask = I2C_DATA_REGION[i];
        if (I2C_DATA_REGION[i] != 0xFF) {
            for (int bit = 0; bit < 8; bit++) {
                if (!(mask & (1 << bit))) {
                    // Mark this bit as allocated
                    I2C_DATA_REGION[i] |= (1 << bit);
                    // Calculate command index
                    int cmd_idx = (i * 8) + bit;
                    return &conf->data_start[cmd_idx];
                }
            }
        }
    }
    return NULL;  // No space.
}

/**
 * Given a pointer to a command in the data region, release this command to the allocator.
 */
static void __libi2c_free_cmd(libi2c_conf_t *conf, i2c_cmd_t *cmd)
{
    // Make sure command is actually in the data region.
    assert((uintptr_t)cmd > (uintptr_t)I2C_DATA_REGION
           && ((uintptr_t)cmd - (uintptr_t)I2C_DATA_REGION) <= i2c_config.data.size);

    size_t cmd_idx = cmd - conf->data_start;
    size_t bitmask_byte = cmd_idx / 8;
    uint8_t bitmask_bit = cmd_idx % 8;
    I2C_DATA_REGION[bitmask_byte] &= ~(1 << bitmask_bit);
}

// ########### I2C interface ###########

static inline int check_meta_buf(void *meta_buf)
{
    if ((uintptr_t)meta_buf < (uintptr_t)I2C_META_REGION
        || (uintptr_t)meta_buf > ((uintptr_t)I2C_META_REGION + i2c_config.meta.size)) {
        LOG_LIBI2C_ERR("i2c_write called with meta_buf not in meta region!");
        return -1;
    }
    return 0;
}

/**
 * Given a buffer pointer from the META region, create an I2C op, dispatch and return when
 * complete. This is a blocking function call. Implements all single-cmd ops.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
static int __i2c_dispatch(libi2c_conf_t *conf, i2c_addr_t address, void *buf, uint16_t len, uint8_t flag_mask)
{
    // Check that supplied buffer is within bounds of meta region
    if (check_meta_buf(buf)) {
        return -1;
    }
    // Create a write command
    i2c_cmd_t *cmd = __libi2c_alloc_cmd(conf);
    if (cmd == NULL) {
        LOG_LIBI2C_ERR("__i2c_dispatch failed to allocate command!\n");
        return -1;
    }
    size_t meta_offset = (uint8_t *)buf - I2C_META_REGION;
    i2c_err_t error = 0;
    cmd->offset = meta_offset;
    cmd->len = len;
    cmd->flag_mask = flag_mask;

    if (i2c_enqueue_request(*conf->handle, address, (uintptr_t)cmd, (uintptr_t)I2C_META_REGION, 1)) {
        LOG_LIBI2C_ERR("__i2c_dispatch failed to enqueue request!\n");
        error = -1;
        goto i2c_dispatch_fail;
    }
    microkit_notify(i2c_config.virt.id);

    // Await response.
    microkit_cothread_wait_on_channel(i2c_config.virt.id);

    i2c_addr_t returned_addr = 0;
    size_t err_cmd = 0;     // Irrelevant for single-command runs.
    if (i2c_dequeue_response(*conf->handle, &returned_addr, &error, &err_cmd)) {
        LOG_LIBI2C_ERR("__i2c_dispatch failed to dequeue response!\n");
        error = -1;
        goto i2c_dispatch_fail;
    }
    assert(returned_addr == address);   // If this ever fails, the protocol is broken or misused!
i2c_dispatch_fail:
    __libi2c_free_cmd(conf, cmd);
    return error;
}

/**
 * Perform a simple I2C write given a META region buffer containing data.
 * To perform a write to a device register, ensure the FIRST byte of write_buf contains
 * the register address.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int i2c_write(libi2c_conf_t *conf, i2c_addr_t address, void *write_buf, uint16_t len)
{
    return __i2c_dispatch(conf, address, write_buf, len, I2C_FLAG_STOP);
}

/**
 * Perform a simple I2C read given a META region buffer to store result.
 * To perform a read to a device register, use i2c_writeread!
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int i2c_read(libi2c_conf_t *conf, i2c_addr_t address, void *read_buf, uint16_t len)
{
    return __i2c_dispatch(conf, address, read_buf, len, I2C_FLAG_STOP | I2C_FLAG_READ);
}

/**
 * Perform an I2C read given a META region buffer to store result, writing the address of a
 * peripheral register first.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int i2c_writeread(libi2c_conf_t *conf, i2c_addr_t address, i2c_addr_t reg_address, void *read_buf, uint16_t len)
{
    // Check that supplied buffer is within bounds of meta region
    if (check_meta_buf(read_buf)) {
        return -1;
    }
    // Inject register address to read buf
    ((i2c_addr_t *)read_buf)[0] = reg_address;

    return __i2c_dispatch(conf, address, read_buf, len, I2C_FLAG_STOP | I2C_FLAG_READ | I2C_FLAG_WRRD);
}

/**
 *  Perform a raw I2C dispatch with custom flags.
 */
int i2c_dispatch(libi2c_conf_t *conf, i2c_addr_t address, void *buf, uint16_t len, uint8_t flag_mask)
{
    return __i2c_dispatch(conf, address, buf, len, flag_mask);
}
