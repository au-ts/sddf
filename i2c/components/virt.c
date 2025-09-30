/*
 * Copyright 2025, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
#include <microkit.h>
#include <stdbool.h>
#include <stddef.h>
#include <sddf/i2c/i2c_virt.h>
#include <sddf/util/util.h>
#include <sddf/util/printf.h>

// #define DEBUG_VIRT

#ifdef DEBUG_VIRT
#define LOG_VIRT(...) do{ sddf_dprintf("I2C VIRT|INFO: "); sddf_dprintf(__VA_ARGS__); }while(0)
#else
#define LOG_VIRT(...) do{}while(0)
#endif

#define LOG_VIRT_ERR(...) do{ sddf_printf("I2C VIRT|ERROR: "); sddf_printf(__VA_ARGS__); }while(0)


__attribute__((__section__(".i2c_virt_config"))) i2c_virt_config_t config;

// sDDF queues
i2c_queue_handle_t client_queues[SDDF_I2C_MAX_CLIENTS];
i2c_queue_handle_t driver_queue;

// Internal queue of deferred work
virt_q_t deferred_queue;

// Intermediate buffer: used to store commands while transaction is parsed and validated.
i2c_cmd_t intermediary[I2C_QUEUE_SZ];
size_t intermediary_idx = 0;

// Security list: owner of each i2c address on the bus
int security_list[I2C_BUS_ADDRESS_MAX + 1];

static inline void purge_intermediary(void)
{
    intermediary_idx = 0;
}

static inline int return_error(i2c_err_t err, int client_id, i2c_addr_t bus_addr, uint8_t err_idx)
{
    purge_intermediary();
    int ret = i2c_enqueue_response(client_queues[client_id], bus_addr, err, err_idx);
    microkit_notify(CLIENT_CH_OFFSET + client_id);
    return ret;
}

static inline void transmit_intermediary(void) {
    LOG_VIRT("transmit_intermediary: committing %zu entries...\n", intermediary_idx);
    for (int i = 0; i <= intermediary_idx; i++) {
        int err = i2c_enqueue_request(driver_queue, intermediary[i]);
        /* If this assert fails we have a race as the driver should only ever be dequeuing */
        assert(!err);
    }
    intermediary_idx = 0;
    // Commit enqueued entries as a batch.
    i2c_request_commit(driver_queue);
    assert(driver_queue.request->ctrl.tail == driver_queue.request->staged_active_tail);
    LOG_VIRT("Done! tail = %u : staged tail = %u\n", driver_queue.request->ctrl.tail, driver_queue.request->staged_active_tail);
}

/**
 *  Process requests from a given client. Pops off commands one at a time searching for headers.
 *  Headers will be process immediately, unless:
 *  a. The driver queue cannot fit the request, in which case we defer to try again once
 *     the driver has returned control to the virt.
 *  b. The request was behind the a request which was deferred, in which case it will also
 *     be processed after the driver returns data to the virt.
 *
 *  Errors will be returned to the client immediately if:
 *  1. Header is invalid (bad config).
 *  2. Not enough data for header (client didn't enqueue enough data).
 *  3. Any command is invalid.
 *
 *  Otherwise, we accumulate valid commands until a full transaction is composed and send
 *  them once all are found. As each command is processed, we replace the client offset
 *  with one the virt can understand.
 *
 *  @param client_id: client id passed from `notified()`
 *  @param deferred: handle work from deferred queue if true, else handle all work.
 *  @param force_defer: find the next header and defer unconditionally.
 *  @returns int: 0 if exited normally, nonzero if work was deferred or queue dequeue failed.
 */
int process_request(uint32_t client_id, i2c_cmd_t *deferred_cmd, size_t deferred_work,
                    bool force_defer)
{
    assert(client_id < config.num_clients);
    assert(intermediary_idx == 0);
    // Request processing vars
    bool enqueued = false;  // Transaction sent to driver
    bool deferred = false;  // Transaction had to be deferred
    size_t cmd_count = 0;       // Number of commands processed so far
    size_t batch_remaining = 0; // Tokens left to extract from current header
    i2c_cmd_t cmd;
    i2c_cmd_t *prev_cmd = NULL;
    i2c_addr_t bus_address = 0;

    size_t max_work = I2C_QUEUE_SZ;

    // Load deferred command.
    if (deferred_work != 0) {
        assert(!force_defer);   // Should not be used wiwth deferred answer.
        max_work = deferred_work;
        intermediary[0] = *deferred_cmd;
        intermediary_idx = 1;
        batch_remaining = deferred_cmd->payload.i2c_header.batch_len;
        assert(cmd_count <= max_work);
    }

    LOG_VIRT("New request arrived from client %d\n", client_id);
    /* Do not process the request if we cannot pass it to the driver */
    while (!i2c_queue_empty(client_queues[client_id].request->ctrl) &&
           !i2c_request_queue_full(driver_queue) &&
           cmd_count < max_work) {
        int err = i2c_dequeue_request(client_queues[client_id], &cmd);
        LOG_VIRT("Batch remaining: %zu. Command dequeued:\n", batch_remaining);
        LOG_VIRT("\tData: %p\n", (cmd.flag_mask & I2C_FLAG_HEAD) ? (void *)0xDEADBEEF : cmd.payload.data);
        LOG_VIRT("\tFlag mask: %u \n", cmd.flag_mask);
        LOG_VIRT("\tHEAD: %d\n\t\tREAD: %d\n\t\tWRRD: %d\n\t\tSTOP: %d\n",
                 (cmd.flag_mask & I2C_FLAG_HEAD), (cmd.flag_mask & I2C_FLAG_READ),
                 (cmd.flag_mask & I2C_FLAG_WRRD), (cmd.flag_mask & I2C_FLAG_STOP));
        LOG_VIRT("\tRSTART: %d\n", (cmd.flag_mask & I2C_FLAG_RSTART));


        cmd_count++;
        if (err) {
            LOG_VIRT_ERR("could not dequeue from request queue\n");
            return -1;
        }

        // This loop has two states: searching for a header or parsing a
        // command once a valid header is found.
        if (batch_remaining == 0) {
            LOG_VIRT("New batch\n");
            // If we're returning after just finishing, send last validated transaction.
            if (intermediary_idx != 0) {
                transmit_intermediary();
                enqueued = true;
                prev_cmd = NULL;
            }
            // Invariant. Should never be violated after transmitting or entering initially.
            assert(intermediary_idx == 0);

            // Pop commands until a head is encountered - i.e. discard remains of
            // any previous malformed requests.
            int head_len = i2c_parse_cmd_header(&cmd);
            bus_address = cmd.payload.i2c_header.address;
            if (head_len == 0) {
                // Case 1: this is not a header. Discard silently.
                LOG_VIRT("\tCommand is not a header, discarding...\n");
                continue;
            } else if (head_len < 0) {
                // Case 2: invalid header. Send response to client
                LOG_VIRT_ERR("Invalid header received! Dropping request...\n");
                return_error(I2C_ERR_MALFORMED_HEADER, client_id, bus_address, 0);
                continue;
            }
            LOG_VIRT("\theader: addr %u with %u bytes\n", bus_address, head_len);

            // Check that client can access target device
            if (bus_address > I2C_BUS_ADDRESS_MAX || security_list[bus_address] != client_id) {
                LOG_VIRT_ERR("invalid bus address (0x%x) requested by client 0x%x\n", bus_address, client_id);
                return_error(I2C_ERR_UNPERMITTED_ADDR, client_id, bus_address, 0);
                continue;
            }

            // Ensure that the client has supplied enough commands for this transaction and
            // this invocation has has enough max work to complete it. If we don't have enough
            // max work, the command was malformed / impartially transmitted.
            // Add 1 to handle presence of this header cmd for client_q_len.
            // TODO: checking cmd count here is wrong
            size_t client_q_len = i2c_queue_length(client_queues[client_id].request->ctrl);
            if (client_q_len < head_len || max_work - cmd_count < head_len) {
                // Inadequate.
                LOG_VIRT_ERR("Request specifies %u requests but client queue only contains %zu commands!\n",
                             head_len + 1, client_q_len);
                return_error(I2C_ERR_MALFORMED_TRANSACTION, client_id, cmd.payload.i2c_header.address, 0);
                continue;
            }

            // Header command is valid!
            batch_remaining = head_len;

            // Finally: determine if the driver queue can fit this command. If not, we go to
            // sleep here and defer the work until the driver has returned.
            // IMPORTANT: need to track intermediary fullness here too.
            if (force_defer || I2C_QUEUE_SZ - i2c_request_queue_length(driver_queue) < head_len + 1) {
                LOG_VIRT("Driver queue cannot accept command. Deferring\n");
                // We defer all work here, not just the current command. We list the current
                // command separately as we cannot enqueue it again safely.
                // note: this is not an off by one error! we don't include the head command in length.
                int ret = virt_q_append(&deferred_queue, client_id, client_q_len, cmd);
                if (ret < 0) {
                    batch_remaining = 0;
                    LOG_VIRT_ERR("Failed to enqueue deferred work correctly! Virt is broken. Discarded %d commands of work...", head_len + 1);
                    return_error(I2C_ERR_OTHER, client_id, bus_address, 0);
                    continue;
                }
                deferred = true;
                break;
            }
            // Add header to intermediary queue.
            intermediary[0] = cmd;
            intermediary_idx = 1;
            continue;
        } else {
            // Case 2: we're validating a transaction after finding a valid header.
            // For each command, check it is sane and send to intermediary queue
            if ((uintptr_t) cmd.payload.data > (config.clients[client_id].client_data_vaddr + config.clients[client_id].data_size)) {
                batch_remaining = 0;
                return_error(I2C_ERR_MALFORMED_TRANSACTION, client_id, bus_address, 0);
                LOG_VIRT_ERR("invalid data pointer (%p) given by client %u.", cmd.payload.data, client_id);
                continue;
            }

            // Check flags are sane
            // Invariant: cmd will never have the header bit set here.
            assert(!(cmd.flag_mask & I2C_FLAG_HEAD));
            if (cmd.flag_mask & I2C_FLAG_HEAD) {
                batch_remaining = 0;
                return_error(I2C_ERR_MALFORMED_TRANSACTION, client_id, bus_address, 0);
                LOG_VIRT_ERR("Body command has an invalid flag set!");
                continue;
            }
            // Repeated starts are only valid if the previous command was in the same direction.
            if (cmd.flag_mask & I2C_FLAG_RSTART) {
                // If there was no previous command or the previous command
                // has a different data direction, this RSTART is invalid.
                if (prev_cmd == NULL ||
                    (prev_cmd->flag_mask & (I2C_FLAG_READ|I2C_FLAG_WRRD)) !=
                    (cmd.flag_mask & I2C_FLAG_READ)) {
                    batch_remaining = 0;
                    return_error(I2C_ERR_MALFORMED_TRANSACTION, client_id, bus_address, 0);
                    LOG_VIRT_ERR("Repeated start condition with invalid precessor!");
                    continue;
                }
                // Write-read operations cannot ever be a repeated start as
                // they imply a repeated start anyway (and change dir!)
                if (cmd.flag_mask & I2C_FLAG_WRRD) {

                    batch_remaining = 0;
                    return_error(I2C_ERR_MALFORMED_TRANSACTION, client_id, bus_address, 0);
                    LOG_VIRT_ERR("A write-read cannot have FLAG_RSTART!");
                    continue;
                }
            }

            // Convert client pointer to driver pointer
            size_t offset = (size_t) cmd.payload.data - config.clients[client_id].client_data_vaddr;
            if (offset > config.clients[client_id].data_size) {
                LOG_VIRT_ERR("Requested offset of %zu is larger than client data region!\n", offset);
                batch_remaining = 0;
                return_error(I2C_ERR_MALFORMED_TRANSACTION, client_id, bus_address, 0);
                continue;
            }

            uint8_t *new_addr = (uint8_t *)(offset + (size_t)config.clients[client_id].driver_data_vaddr);
            LOG_VIRT("\t Pointer map: %p -> %p\n", cmd.payload.data, new_addr);
            cmd.payload.data = new_addr;

            // Add to intermediary at last.
            intermediary[intermediary_idx] = cmd;
            prev_cmd = &intermediary[intermediary_idx];
            batch_remaining--;
            intermediary_idx++;
            LOG_VIRT("\tEnqueued command %zu\n", intermediary_idx);
        }
    }
    // Trigger send of final batch if it completed successfully.
    if (batch_remaining == 0 && intermediary_idx != 0) {
        LOG_VIRT("Last request done. Transmitting...\n");
        transmit_intermediary();
        enqueued = true;
    } else {
        // Command was malformed somehow. This should never happen!
        assert(intermediary_idx != 0);
    }

    // Successfully validated command(s). Send.
    // Invariant: only commands validated as small enough to fit in the driver queue exist in intermediary
    if (enqueued) {
        microkit_deferred_notify(config.driver.id);
    }
    return deferred;
}

void process_response()
{
    /*
     * Process all responses that the driver has queued up. We look at which client currently has the
     * claim on the bus and deliver the response to them. If a client's response queue is full we
     * simply drop the response (a typical client will never reach that scenario unless it has some
     * catastrophic bug or is malicious).
     */
    LOG_VIRT("PROCESS RESPONSE\n");
    while (!i2c_queue_empty(driver_queue.response->ctrl)) {
        LOG_VIRT("Handling response...\n");
        i2c_addr_t bus_address = 0;
        i2c_err_t error = 0;
        size_t err_cmd = 0;

        /* We trust the driver to give us a sane bus address */
        int err = i2c_dequeue_response(driver_queue, &bus_address, &error, &err_cmd);
        /* If this assert fails we have a race as the virtualiser should be the only one dequeuing
         * from the driver's response queue */
        assert(!err);

        size_t client_id = security_list[bus_address];
        if (client_id == BUS_UNCLAIMED) {
            LOG_VIRT_ERR("Driver response (addr=%u) belongs to no authenticated client!\n", bus_address);
            /* The client has released the bus before receiving all their responses, so we simply
             * drop the response. */
            continue;
        }

        /* There is no point checking if the enqueue succeeds or not. */
        i2c_enqueue_response(client_queues[client_id], bus_address, error, err_cmd);

        LOG_VIRT("Notifying client.\n");
        microkit_notify(CLIENT_CH_OFFSET + client_id);
    }
}

void init(void)
{
    assert(i2c_config_check_magic(&config));
    assert(config.driver.id == 0);  // @leslr: is this needed? sdfgen should remove any need
    LOG_VIRT("initialising\n");
    for (int i = 0; i < I2C_BUS_ADDRESS_MAX + 1; i++) {
        security_list[i] = BUS_UNCLAIMED;
    }
    driver_queue = i2c_queue_init(config.driver.req_queue.vaddr, config.driver.resp_queue.vaddr);
    for (int i = 0; i < config.num_clients; i++) {
        /*LOG_VIRT("Initialising client %d -> DATA region: %p\n", i, config.)*/
        client_queues[i] = i2c_queue_init(config.clients[i].conn.req_queue.vaddr,
                                          config.clients[i].conn.resp_queue.vaddr);
    }
}

/**
 *  Since i2c is a synchronous bus, we must take great care to ensure incoming work is
 *  processed monotonically to avoid the possibility of starvation. Additionally, since
 *  commands are strictly dependent on each other, we can only ever move entire batches
 *  of valid commands between queues.
 *
 *  To handle these constraints, we only ever accept requests if the driver queue can fit
 *  all commands involved and never allow requests to be accepted in a partial state.
 *
 *  This loop will always handle the driver response first to make room, and then will
 *  handle any deferred requests in the deferred request queue. New requests are handled
 *  last and are sent straight to the deferred queue if we couldn't deplete all deferred
 *  work first.
 */
void notified(microkit_channel ch)
{
    bool driver_q_exhausted = false;
    // Handle response first
    if (ch == config.driver.id) {
        LOG_VIRT("notified by driver\n");
        process_response();
    }
    // Check for deferred work and process it.
    while (!virt_q_empty(&deferred_queue)) {
        uint32_t client_id;
        size_t num_cmds;
        i2c_cmd_t head_cmd;
        // Check we can actually fit the next batch of deferred work before
        // starting. Otherwise we can end up running for absurdly long as work
        // is re-queued and is no longer processed monotonically!
        virt_q_peek(&deferred_queue, &client_id, &num_cmds, &head_cmd);
        if (num_cmds > i2c_request_queue_length(driver_queue)) {
            LOG_VIRT("Deferred entry is too big to be handled now. Giving up.");
            driver_q_exhausted = true;
            break;
        }

        int deferred = process_request(client_id, &head_cmd, num_cmds, false);
        // Leave early if we ran out of work again.
        if (deferred) {
            LOG_VIRT("Driver queue is exhausted after handling deferred request.");
            driver_q_exhausted = true;
            break;
        }
    }

    if (ch != config.driver.id) {
        uint32_t client_id = ch - CLIENT_CH_OFFSET;
        LOG_VIRT("notified by client %u\n", client_id);
        // If we couldn't fulfill deferred requests, we shouldn't process this
        // request to maintain monotonicity. A client can starve all others that
        // use large requests if we don't bail out here. We do this by setting force_defer
        if (driver_q_exhausted) {
            LOG_VIRT("Pending request from client %u deferred to maintain run order.", client_id);
        }
        process_request(client_id, NULL, 0, driver_q_exhausted);
    }
}

// TODO: replace this with sdf_gen method for bus address assignment once
// sdf_gen refactor is complete.
seL4_MessageInfo_t protected(microkit_channel ch, seL4_MessageInfo_t msginfo)
{
    size_t label = microkit_msginfo_get_label(msginfo);
    size_t bus = microkit_mr_get(I2C_BUS_SLOT);
    uint32_t client_id = ch - CLIENT_CH_OFFSET;

    if (label != I2C_BUS_CLAIM && label != I2C_BUS_RELEASE) {
        LOG_VIRT_ERR("unknown label (0x%lx) given by client on channel 0x%x\n", label, ch);
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    if (bus > I2C_BUS_ADDRESS_MAX) {
        LOG_VIRT_ERR("invalid bus address (0x%lx) given by client on "
                     "channel 0x%x. Max bus address is 0x%x\n",
                     bus, ch, I2C_BUS_ADDRESS_MAX);
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    switch (label) {
    case I2C_BUS_CLAIM:
        // We have a valid bus address, we need to make sure no one else has claimed it.
        LOG_VIRT("Client %u claimed address %u\n", client_id, bus);
        if (security_list[bus] != BUS_UNCLAIMED) {
            LOG_VIRT_ERR("bus address 0x%lx already claimed, cannot claim for channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(I2C_FAILURE, 0);
        }

        security_list[bus] = client_id;
        break;
    case I2C_BUS_RELEASE:
        if (security_list[bus] != client_id) {
            LOG_VIRT_ERR("bus address 0x%lx is not claimed by channel 0x%x\n", bus, ch);
            return microkit_msginfo_new(I2C_FAILURE, 0);
        }

        security_list[bus] = BUS_UNCLAIMED;
        break;
    default:
        LOG_VIRT_ERR("reached unreachable case\n");
        return microkit_msginfo_new(I2C_FAILURE, 0);
    }

    return microkit_msginfo_new(I2C_SUCCESS, 0);
}
