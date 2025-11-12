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

typedef struct ext4_fs_cmd_params_file_open {
    fs_buffer_t path;
    uint32_t parent_inode_num;
    bool create;
    uint16_t ftype;
    uint32_t name_off;
    uint8_t _padding[4];
    uint64_t inode;
} ext4_fs_cmd_params_file_open_t;

typedef struct ext4_fs_cmd_params_file_read {
    uint32_t inode;
    uint64_t _padding;
    uint64_t offset;
    fs_buffer_t read_buf;  
    uint64_t n;             
} ext4_fs_cmd_params_file_read_t;

typedef struct ext4_fs_cmd_params_file_write {
    uint32_t inode;
    uint64_t _padding;   
    uint64_t offset;
    fs_buffer_t write_buf;   
    uint64_t n;                
} ext4_fs_cmd_params_file_write_t;

typedef union ext4_fs_cmd_params {
    ext4_fs_cmd_params_file_open_t file_open;
    ext4_fs_cmd_params_file_read_t file_read;
    ext4_fs_cmd_params_file_write_t file_write;
    uint8_t min_size[48];
} ext4_fs_cmd_params_t;

typedef struct ext4_fs_cmd {
    uint64_t id;
    uint64_t type;
    ext4_fs_cmd_params_t params;
} ext4_fs_cmd_t;

typedef struct ext4_fs_cmpl {
    uint64_t id;
    uint64_t status;
    ext4_fs_cmd_params_t data;
} ext4_fs_cmpl_t;

typedef union ext4_fs_msg {
    ext4_fs_cmd_t cmd;
    ext4_fs_cmpl_t cmpl;
} ext4_fs_msg_t;

typedef struct ext4_fs_queue {
    uint64_t head;
    uint64_t tail;
    uint8_t padding[48];
    ext4_fs_msg_t buffer[FS_QUEUE_CAPACITY];
} ext4_fs_queue_t;

ext4_fs_queue_t *fs_command_queue;
ext4_fs_queue_t *fs_completion_queue;

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

uint64_t ext4_fs_queue_length_consumer(ext4_fs_queue_t *queue)
{
    return __atomic_load_n(&queue->tail, __ATOMIC_ACQUIRE) - queue->head;
}

uint64_t ext4_fs_queue_length_producer(ext4_fs_queue_t *queue)
{
    return queue->tail - __atomic_load_n(&queue->head, __ATOMIC_ACQUIRE);
}

ext4_fs_msg_t *ext4_fs_queue_idx_filled(ext4_fs_queue_t *queue, uint64_t index)
{
    index = queue->head + index;
    return &queue->buffer[index % FS_QUEUE_CAPACITY];
}

ext4_fs_msg_t *ext4_fs_queue_idx_empty(ext4_fs_queue_t *queue, uint64_t index)
{
    index = queue->tail + index;
    return &queue->buffer[index % FS_QUEUE_CAPACITY];
}

void ext4_fs_queue_publish_consumption(ext4_fs_queue_t *queue, uint64_t amount_consumed)
{
    __atomic_store_n(&queue->head, queue->head + amount_consumed, __ATOMIC_RELEASE);
}

void ext4_fs_queue_publish_production(ext4_fs_queue_t *queue, uint64_t amount_produced)
{
    __atomic_store_n(&queue->tail, queue->tail + amount_produced, __ATOMIC_RELEASE);
}

void init(void) {
    assert(fs_config_check_magic(&fs_config));
    assert(blk_config_check_magic(&blk_config));

    assert(blk_config.virt.num_buffers >= FAT_WORKER_THREAD_NUM);

    max_cluster_size = blk_config.data.size / FAT_WORKER_THREAD_NUM;
    fs_command_queue = fs_config.clients.command_queue.vaddr;
    fs_completion_queue = fs_config.clients.completion_queue.vaddr;
    fs_share = fs_config.clients.share.vaddr;

    blk_data = blk_config.data.vaddr;

    blk_queue_init(&blk_queue, blk_config.virt.req_queue.vaddr, blk_config.virt.resp_queue.vaddr, blk_config.virt.num_buffers);

    blk_storage_info = blk_config.virt.storage_info.vaddr;

    /* Wait for the the block device before doing anything else */
    while (!blk_storage_is_ready(blk_storage_info));

    /*
       This part of the code is for setting up the thread pool by
       assign stacks and size of the stack to the pool
    */
    stack_ptrs_arg_array_t costacks = {
        (uintptr_t) &worker_thread_stack_one,
        (uintptr_t) &worker_thread_stack_two,
        (uintptr_t) &worker_thread_stack_three,
        (uintptr_t) &worker_thread_stack_four
    };

    // Init thread pool
    microkit_cothread_init(&co_controller_mem, FAT_WORKER_THREAD_STACKSIZE, costacks);
    for (uint32_t i = 0; i < (FAT_WORKER_THREAD_NUM + 1); i++) {
        microkit_cothread_semaphore_init(&sem[i]);
    }
}