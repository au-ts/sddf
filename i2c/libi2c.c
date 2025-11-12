/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <sddf/i2c/libi2c.h>

// #define DEBUG_LIBI2C
#ifdef DEBUG_LIBI2C
#define LOG_LIBI2C(...) do{ sddf_dprintf("LIBI2C|INFO: "); sddf_printf(__VA_ARGS__); }while(0)
#else
#define LOG_LIBI2C(...) do{}while(0)
#endif

/**
 * Initialise libI2C and return the conf struct needed for all operations.
 */
int libi2c_init(libi2c_conf_t *conf_struct, i2c_queue_handle_t *queue_handle)
{
    conf_struct->handle = queue_handle;
    conf_struct->data_start = (void *)I2C_DATA_REGION;
    return 0;
}

static inline int check_data_buf(void *data_buf)
{
    if ((uintptr_t)data_buf < (uintptr_t)I2C_DATA_REGION
        || (uintptr_t)data_buf > ((uintptr_t)I2C_DATA_REGION + i2c_config.data.size)) {
        LOG_LIBI2C_ERR("sddf_i2c_write called with data_buf not in data region!");
        return -1;
    }
    return 0;
}

/**
 *  Block on a notification using libco or libmicrokitco for blocking calls.
 */
static void __i2c_block(libi2c_conf_t *conf)
{
    LOG_LIBI2C("Dispatching request to virt...\n");
    microkit_notify(i2c_config.virt.id);

    // Await response.
#ifdef LIBI2C_RAW
    co_switch(t_event);
#else
    microkit_cothread_wait_on_channel(i2c_config.virt.id);
#endif
}

/**
 * Given a buffer pointer from the DATA region, create an I2C op, dispatch and return when
 * complete. This is a blocking function call. Implements all single-cmd ops.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
static int __i2c_dispatch(libi2c_conf_t *conf, i2c_addr_t address, void *buf, uint16_t len, uint8_t flag_mask)
{
    LOG_LIBI2C("Dispatch: to=%zu, buf = %p, flag_mask = %zu, len = %zu\n", address, buf, flag_mask, len);
    // Check that supplied buffer is within bounds of data region
    if (check_data_buf(buf)) {
        return -1;
    }
    uint16_t num_batches = (len / 255) + 1; // Number of 255 long batches. cmd_t indexes with uint8

    // Give up if queue cannot fit this many commands. Add 1 for header.
    if (I2C_QUEUE_CAPACITY - i2c_request_queue_length(*conf->handle) < num_batches + 1) {
        return -1;
    }

    // Create header command
    i2c_cmd_t header;
    i2c_err_t error = I2C_ERR_OK;
    header.flag_mask = I2C_FLAG_HEAD;
    header.payload.i2c_header.batch_len = num_batches;
    header.payload.i2c_header.address = address;
    if (i2c_enqueue_request(*conf->handle, header)) {
        LOG_LIBI2C("ERROR: failed to enqueue header!\n");
        return -1;
    }

    // Slice buffer into 255 byte long segments and enqueue.
    for (uint16_t i = 0; i < num_batches; i++) {
        LOG_LIBI2C("Slice %zu / %zu\n", i + 1, num_batches);
        uint16_t curr_offset = ((1 << 8) * i);
        // Batch of 255, unless there are fewer commands left.
        uint8_t data_len = (len - curr_offset) >= 255 ? 255 : (uint8_t)(len - curr_offset);
        i2c_cmd_t data;
        data.payload.data = (uint8_t *)(buf + curr_offset);
        data.data_len = data_len;
        // RSTART for all commands but first, STOP for final, and WRRD only for start.
        data.flag_mask = data_len != (255) ? flag_mask & I2C_FLAG_STOP : 0;
        if (i != 0) {
            data.flag_mask |= I2C_FLAG_RSTART;
        } else {
            data.flag_mask |= flag_mask & I2C_FLAG_WRRD;
        }

        // Add read flag if required.
        data.flag_mask |= flag_mask & I2C_FLAG_READ;

        if (i2c_enqueue_request(*conf->handle, data)) {
            // No need to clean up if we fail. We just surrender pending requests
            // and exit.
            LOG_LIBI2C_ERR("__i2c_dispatch failed to enqueue request!\n");
            error = -1;
            i2c_request_abort(*conf->handle);
            return -1;
        }
    }

    i2c_request_commit(*conf->handle);
    return 0;
}

/**
 *  Attempt to dequeue a response and pack up. This should only be used after
 *  a blocking call has woken up or a non-blocking call is finalising.
 */
static i2c_err_t __i2c_handle_response(libi2c_conf_t *conf, i2c_addr_t *returned_addr, size_t *err_cmd_idx)
{
    // NOTE: the i2c protocol doesn't return bytes written/read. Is that an issue..?
    i2c_err_t error = I2C_ERR_OK;
    if (i2c_dequeue_response(*conf->handle, returned_addr, &error, err_cmd_idx)) {
        LOG_LIBI2C_ERR("__i2c_dispatch failed to dequeue response!\n");
        error = I2C_ERR_QUEUE;
    }
    return error;
}

// #### Blocking API using libco/libmicrokitco ####

/**
 * Perform a simple I2C write given a DATA region buffer containing data.
 * To perform a write to a device register, ensure the FIRST byte of write_buf contains
 * the register address.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int sddf_i2c_write(libi2c_conf_t *conf, i2c_addr_t address, void *write_buf, uint16_t len)
{
    int ret = __i2c_dispatch(conf, address, write_buf, len, I2C_FLAG_STOP);
    if (ret) {
        return ret;
    }
    __i2c_block(conf);
    i2c_addr_t returned_addr;
    size_t err_cmd_idx;
    i2c_err_t err = __i2c_handle_response(conf, &returned_addr, &err_cmd_idx);
    assert(returned_addr == address);
    return err;
}

/**
 * Perform a simple I2C read given a DATA region buffer to store result.
 * To perform a read to a device register, use sddf_i2c_writeread!
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int sddf_i2c_read(libi2c_conf_t *conf, i2c_addr_t address, void *read_buf, uint16_t len)
{
    int ret = __i2c_dispatch(conf, address, read_buf, len, I2C_FLAG_STOP | I2C_FLAG_READ);
    if (ret) {
        return ret;
    }
    __i2c_block(conf);
    i2c_addr_t returned_addr;
    size_t err_cmd_idx;
    i2c_err_t err = __i2c_handle_response(conf, &returned_addr, &err_cmd_idx);
    assert(returned_addr == address);
    return err;
}

/**
 * Perform an I2C read given a DATA region buffer to store result, writing the address of a
 * peripheral register first.
 * This is a blocking function call.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int sddf_i2c_writeread(libi2c_conf_t *conf, i2c_addr_t address, i2c_addr_t reg_address, void *read_buf, uint16_t len)
{
    // Check that supplied buffer is within bounds of data region
    if (check_data_buf(read_buf)) {
        return -1;
    }
    // Inject register address to read buf
    ((i2c_addr_t *)read_buf)[0] = reg_address;

    int ret = __i2c_dispatch(conf, address, read_buf, len, I2C_FLAG_STOP | I2C_FLAG_READ | I2C_FLAG_WRRD);
    if (ret) {
        return ret;
    }
    __i2c_block(conf);
    i2c_addr_t returned_addr;
    size_t err_cmd_idx;
    i2c_err_t err = __i2c_handle_response(conf, &returned_addr, &err_cmd_idx);
    assert(returned_addr == address);
    return err;
}

/**
 *  Perform a raw I2C dispatch with custom flags.
 *  This is a blocking function call.
 */
int sddf_i2c_dispatch(libi2c_conf_t *conf, i2c_addr_t address, void *buf, uint16_t len, uint8_t flag_mask)
{
    int ret = __i2c_dispatch(conf, address, buf, len, flag_mask);
    if (ret) {
        return ret;
    }
    __i2c_block(conf);
    i2c_addr_t returned_addr;
    size_t err_cmd_idx;
    i2c_err_t err = __i2c_handle_response(conf, &returned_addr, &err_cmd_idx);
    assert(returned_addr == address);
    return err;
}

// #### Non-blocking API ####
/**
 * Perform a simple I2C write given a DATA region buffer containing data.
 * To perform a write to a device register, ensure the FIRST byte of write_buf contains
 * the register address.
 * A response can be retrieved after the i2c notification arises using
 * sddf_i2c_nb_return if this function returns successfully.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int sddf_i2c_nb_write(libi2c_conf_t *conf, i2c_addr_t address, void *write_buf, uint16_t len)
{
    return __i2c_dispatch(conf, address, write_buf, len, I2C_FLAG_STOP);
}

/**
 * Perform a simple I2C read given a DATA region buffer to store result.
 * To perform a read to a device register, use sddf_i2c_writeread!
 * A response can be retrieved after the i2c notification arises using
 * sddf_i2c_nb_return if this function returns successfully.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int sddf_i2c_nb_read(libi2c_conf_t *conf, i2c_addr_t address, void *read_buf, uint16_t len)
{
    return __i2c_dispatch(conf, address, read_buf, len, I2C_FLAG_STOP | I2C_FLAG_READ);
}

/**
 * Perform an I2C read given a DATA region buffer to store result, writing the address of a
 * peripheral register first.
 * A response can be retrieved after the i2c notification arises using
 * sddf_i2c_nb_return if this function returns successfully.
 * @return -1 if queue ops fail, positive value corresponding to i2c_err_t, or 0 if successful.
 */
int sddf_i2c_nb_writeread(libi2c_conf_t *conf, i2c_addr_t address, i2c_addr_t reg_address, void *read_buf, uint16_t len)
{
    // Check that supplied buffer is within bounds of data region
    if (check_data_buf(read_buf)) {
        return -1;
    }
    // Inject register address to read buf
    ((i2c_addr_t *)read_buf)[0] = reg_address;

    return __i2c_dispatch(conf, address, read_buf, len, I2C_FLAG_STOP | I2C_FLAG_READ | I2C_FLAG_WRRD);
}

/**
 * Perform a raw I2C dispatch with custom flags.
 * A response can be retrieved after the i2c notification arises using
 * sddf_i2c_nb_return if this function returns successfully.
 */
int sddf_i2c_nb_dispatch(libi2c_conf_t *conf, i2c_addr_t address, void *buf, uint16_t len, uint8_t flag_mask)
{
    return __i2c_dispatch(conf, address, buf, len, flag_mask);
}

/**
 *  Return the most recent queue response from the I2C queue.
 *  Use this after a non-blocking (_nb_) i2c operation has finished,
 *  indicated by the i2c virtualiser sending a notification.
 *  Beware: this function is not smart enough to match multiple overlapping
 *  requests to their responses! The nature of the queues means it is likely
 *  to, but it is not guaranteed.
 *  @return i2c_err_t from driver or -1 on failure.
 */
int sddf_i2c_nb_return(libi2c_conf_t *conf, i2c_addr_t *returned_addr, size_t *err_cmd_idx)
{
    return __i2c_handle_response(conf, returned_addr, err_cmd_idx);
}
