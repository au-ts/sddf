#include <sddf/blk/queue.h>
#include <sddf/blk/config.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <os/sddf.h>
#include <libmicrokitco.h>
#include <sddf/blk/storage_info.h>
#include <protocol.h>
#include <config.h>
#include <decl.h>
#include <ff.h>
#include <diskio.h>

#include <sddf/include/sddf/util/util.h>

__attribute__((__section__(".fs_server_config"))) fs_server_config_t fs_config;
__attribute__((__section__(".blk_client_config"))) blk_client_config_t blk_config;

typedef uintptr_t stack_ptrs_arg_array_t[5 - 1];

co_control_t co_controller_mem;
microkit_cothread_sem_t sem[4 + 1];

blk_queue_handle_t blk_queue;
blk_storage_info_t *blk_storage_info;
char *blk_data;

fs_queue_t *fs_command_queue;
fs_queue_t *fs_completion_queue;
char *fs_share;

char worker_thread_stack_one[0x40000];
char worker_thread_stack_two[0x40000];
char worker_thread_stack_three[0x40000];
char worker_thread_stack_four[0x40000];

uint64_t max_cluster_size;

bool blk_request_pushed = false;

typedef enum {
    FREE,
    INUSE
} space_status;

typedef struct FS_request{
    /* Client side cmd info */
    uint64_t cmd;
    /* Used for passing data to worker threads and receiving responses */
    co_data_t shared_data;
    /* Used to track request_id */
    uint64_t request_id;
    /* Thread handle */
    microkit_cothread_ref_t handle;
    /* Self metadata */
    space_status stat;
} fs_request;

fs_request request_pool[4];

/* Wrapper functions to get around inline for FFI */

bool blk_storage_is_ready_wrapper(blk_storage_info_t *storage_info)
{
    return blk_storage_is_ready(storage_info);
}

void blk_queue_init_wrapper(blk_queue_handle_t *h,
                            blk_req_queue_t *request,
                            blk_resp_queue_t *response,
                            uint32_t capacity)
{
    blk_queue_init(h, request, response, capacity);
}

int blk_enqueue_req_wrapper(blk_queue_handle_t *h,
                            blk_req_code_t code,
                            uintptr_t io_or_offset,
                            uint64_t block_number,
                            uint16_t count,
                            uint32_t id)
{
    return blk_enqueue_req(h, code, io_or_offset, block_number, count, id);
}

int blk_dequeue_resp_wrapper(blk_queue_handle_t *h,
                             blk_resp_status_t *status,
                             uint16_t *success_count,
                             uint32_t *id)
{
    return blk_dequeue_resp(h, status, success_count, id);
}

uint32_t blk_queue_length_resp_wrapper(blk_queue_handle_t *h)
{
    return blk_queue_length_resp(h);
}

bool blk_config_check_magic_wrapper(void *config)
{
    return blk_config_check_magic(config);
}

uint64_t fs_queue_length_consumer_wrapper(fs_queue_t *queue)
{
    return fs_queue_length_consumer(queue);
}

uint64_t fs_queue_length_producer_wrapper(fs_queue_t *queue)
{
    return fs_queue_length_producer(queue);
}

fs_msg_t *fs_queue_idx_filled_wrapper(fs_queue_t *queue, uint64_t index)
{
    return fs_queue_idx_filled(queue, index);
}

fs_msg_t *fs_queue_idx_empty_wrapper(fs_queue_t *queue, uint64_t index)
{
    return fs_queue_idx_empty(queue, index);
}

void fs_queue_publish_consumption_wrapper(fs_queue_t *queue, uint64_t amount_consumed)
{
    fs_queue_publish_consumption(queue, amount_consumed);
}

void fs_queue_publish_production_wrapper(fs_queue_t *queue, uint64_t amount_produced)
{
    fs_queue_publish_production(queue, amount_produced);
}