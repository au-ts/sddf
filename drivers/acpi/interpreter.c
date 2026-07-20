
#include <sddf/util/vspace.h>
#include "acpi.h"
// =========================== Refactor =========================

const char acpi_str_adr[] = {'_', 'A', 'D', 'R', 0};  // Address
const char acpi_str_bbn[] = {'_', 'B', 'B', 'N', 0};  // BIOS Bus Number
// TODO: share signatures
const char test_aml_str_crs[] = {'_', 'C', 'R', 'S', 0};  // Current Resource Settings

typedef enum {
    INIT = 0,
    PKT_LEN,
    OBJECT_NAME_STRING, // Name String used for creating objects
    NAME_STRING,        // Name String referring to a namespace node
    TERM_LIST,
    FIELD_LIST,
    TERM_INTEGER,
    BYTE_DATA,
    WORD_DATA,
    DWORD_DATA,
    QWORD_DATA,
    STRING_DATA,
    BUFFER_DATA,
    PACKAGE_DATA,
    DATA_OBJECT,
    COMPLETE,
} parse_stage_t;

#define MAX_OPCODE 256 // 1-byte AML opcode
#define MAX_OP_STAGES 8

parse_stage_t op_stage_table[MAX_OPCODE][MAX_OP_STAGES] = {
    [NULL_OP] = { INIT, TERM_LIST, COMPLETE },
    [RETURN_OP] = { INIT, DATA_OBJECT, COMPLETE },
    [SCOPE_OP] = { INIT, PKT_LEN, OBJECT_NAME_STRING, TERM_LIST, COMPLETE },
    [METHOD_OP] = { INIT, PKT_LEN, OBJECT_NAME_STRING, BYTE_DATA, TERM_LIST, COMPLETE },
    [NAME_OP] = { INIT, OBJECT_NAME_STRING, DATA_OBJECT, COMPLETE},
    [STORE_OP] = { INIT, DATA_OBJECT, NAME_STRING, COMPLETE },
    [IF_OP] = { INIT, PKT_LEN, TERM_INTEGER, TERM_LIST, COMPLETE },
    [ELSE_OP] = { INIT, PKT_LEN, TERM_LIST, COMPLETE },
    [ALIAS_OP] = { INIT, NAME_STRING, NAME_STRING, COMPLETE },
    [CREATE_BIT_FIELD_OP] = { INIT, BUFFER_DATA, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_BYTE_FIELD_OP] = { INIT, BUFFER_DATA, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_WORD_FIELD_OP] = { INIT, BUFFER_DATA, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_DWORD_FIELD_OP] = { INIT, BUFFER_DATA, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_QWORD_FIELD_OP] = { INIT, BUFFER_DATA, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [LEQUAL_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, COMPLETE },
    [AND_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [ADD_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [SUBTRACT_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [SHIFT_LEFT_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [SHIFT_RIGHT_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [BYTE_PREFIX] = { INIT, BYTE_DATA, COMPLETE },
    [WORD_PREFIX] = { INIT, WORD_DATA, COMPLETE },
    [DWORD_PREFIX] = { INIT, DWORD_DATA, COMPLETE },
    [QWORD_PREFIX] = { INIT, QWORD_DATA, COMPLETE },
    [STRING_PREFIX] = { INIT, STRING_DATA, COMPLETE },
    [BUFFER_PREFIX] = { INIT, PKT_LEN, TERM_INTEGER, BUFFER_DATA, COMPLETE },
    [PACKAGE_PREFIX] = { INIT, PKT_LEN, COMPLETE },
    [DEREF_OF_OP] = { INIT, TERM_INTEGER, COMPLETE },
    [INDEX_OP] = { INIT, DATA_OBJECT, TERM_INTEGER, NAME_STRING, COMPLETE },
};

parse_stage_t op_stage_5b_table[MAX_OPCODE][MAX_OP_STAGES] = {
    [FIELD_OP & 0xFF] = { INIT, PKT_LEN, OBJECT_NAME_STRING, BYTE_DATA, FIELD_LIST, COMPLETE},
    [CREATE_FIELD_OP & 0xFF] = { INIT, BUFFER_DATA, TERM_INTEGER, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [INDEX_FIELD_OP & 0xFF] = { INIT, PKT_LEN, COMPLETE},
    [OP_REGION_OP & 0xFF] = { INIT, OBJECT_NAME_STRING, BYTE_DATA, TERM_INTEGER, TERM_INTEGER, COMPLETE},
    [DEVICE_OP & 0xFF] = { INIT, PKT_LEN, OBJECT_NAME_STRING, TERM_LIST, COMPLETE },
    [MUTEX_OP & 0xFF] = { INIT, NAME_STRING, BYTE_DATA, COMPLETE },
    [POWER_RESOURCE_OP & 0xFF] = { INIT, PKT_LEN, NAME_STRING, BYTE_DATA, WORD_DATA, TERM_LIST, COMPLETE },
    [PROCESSOR_OP & 0xFF] = { INIT, PKT_LEN, COMPLETE },
    [THERMAL_ZONE_OP & 0xFF] = { INIT, PKT_LEN, COMPLETE },
};

parse_stage_t op_stage_lnot_table[MAX_OPCODE][MAX_OP_STAGES] = {
    [LNOT_EQUAL_OP & 0xFF] = { INIT, TERM_INTEGER, TERM_INTEGER, COMPLETE },
    [LLESS_EQUAL_OP & 0xFF] = { INIT, TERM_INTEGER, TERM_INTEGER, COMPLETE },
    [LGREATER_EQUAL_OP & 0xFF] = { INIT, TERM_INTEGER, TERM_INTEGER, COMPLETE },
};

parse_stage_t op_stage_custom[MAX_OPCODE][MAX_OP_STAGES] = {
    [PRT_PACKAGE & 0xFF] = { INIT, PKT_LEN, BYTE_DATA, TERM_INTEGER, TERM_INTEGER, DATA_OBJECT, TERM_INTEGER, COMPLETE },
};

parse_state_t *current_state;

mempool_t state_stack_mempool = {
    .start = (void *)0x50000000,
    .next = (void *)0x50000000,
    .end = (void *)0x50010000,
};

#define READ_BITS(val, m, n) (((val) >> (m)) & ((1ULL << (n)) - 1))

scanner_t scanner;

// =============== Memory Pool =============

void *mempool_alloc(mempool_t *mempool, uint32_t mem_size)
{
    if (mempool->next + mem_size >= mempool->end) {
        // Error: Out of memory for AML objects
        return 0;
    }

    void *allocated_mem = mempool->next;
    mempool->next = mempool->next + mem_size;

    for (uint8_t *clear_byte = allocated_mem; clear_byte < (uint8_t *)mempool->next; clear_byte++) {
        *clear_byte = 0;
    }
    return allocated_mem;
}

void mempool_rc(mempool_t *mempool, void *addr, uint32_t mem_size)
{
    if (addr + mem_size < mempool->next) {
        sddf_dprintf("[Error] failed to release memory [0x%lx-0x%lx] from allocated memory pool [0x%lx-0x%lx]\n", (uintptr_t)addr, (uintptr_t)(addr + mem_size), (uintptr_t)mempool->start, (uintptr_t)mempool->next);
        return;
    }

    mempool->next = addr;
}

// =============== Namespace Node ==============

// Return object pointer if already exists
aml_namespace_node_t *find_local_variable_in_namespace(aml_namespace_node_t *node, uint8_t op_code)
{
    if (node == NULL) return NULL;
    if (node->child == NULL) return NULL;

    aml_namespace_node_t *child = node->child;
    while (child) {
        if (child->op_code == op_code) return child;
        child = child->next;
    }

    return NULL;
}

// Return object pointer if already exists
aml_namespace_node_t *find_child_node_by_name(aml_namespace_node_t *node, const char *name_segment)
{
    if (node == NULL) return NULL;
    if (node->child == NULL) return NULL;

    aml_namespace_node_t *child = node->child;
    while (child) {
        if (!strcmp(child->name, name_segment)) return child;
        if (child->op_code == OP_REGION_OP) {
            aml_namespace_node_t *field_node = find_child_node_by_name(child, name_segment);
            if (field_node) {
                return field_node;
            }
        }
        child = child->next;
    }

    return NULL;
}

uint8_t find_decendant_nodes_by_name(aml_namespace_node_t *node, const char *name_segment, aml_namespace_node_t **lookup_results, uint8_t num_results)
{
    if (!strcmp(node->name, name_segment)) {
        lookup_results[num_results] = node;
        num_results++;
    }
    aml_namespace_node_t *child = node->child;
    while (child) {
        num_results = find_decendant_nodes_by_name(child, name_segment, lookup_results, num_results);
        child = child->next;
    }

    return num_results;
}

aml_namespace_node_t *find_namespace_node_by_name(aml_namespace_node_t *node, const char *name_segment)
{
    aml_namespace_node_t *parent = node;
    while (parent) {
        aml_namespace_node_t *target = find_child_node_by_name(parent, name_segment);
        if (target) {
            return target;
        }
        parent = parent->parent;
    }
    return NULL;
}

aml_namespace_node_t *namespace_insert_child_node(aml_namespace_node_t *namespace, const char *name_segment, enum aml_encoding_value op_code)
{
    aml_namespace_node_t *child_node = (aml_namespace_node_t *)mempool_alloc(&aml_namespace_mempool, sizeof(aml_namespace_node_t));
    if (child_node == NULL) {
        sddf_dprintf("Failed to create a new namespace node: Out of Memory\n");
        return NULL;
    }

    child_node->pkt_start = current_state->node_start;
    child_node->parent = namespace;
    child_node->op_code = op_code;
    if (name_segment != NULL) {
        memcpy(&child_node->name, name_segment, 4);
        child_node->name[4] = '\0';
        /* sddf_dprintf("Create a type 0x%02X object: %s at 0x%lx, parent: %s\n", op_code, name_segment, (uintptr_t)scanner.current, namespace->name); */
    } else {
        /* sddf_dprintf("Create a type 0x%02X object\n", op_code); */
    }

    // Insert the new node into the front of list
    if (namespace->child) {
        child_node->next = namespace->child;
    }

    namespace->child = child_node;
    return child_node;
}

// =============== State Stack ===============

parse_stage_t get_op_stage()
{
    if (current_state->op_code == NULL_OP) {
        return INIT;
    }

    if ((current_state->op_code & 0xFF00) == 0x5B00) {
        uint8_t second_op_code = current_state->op_code & 0xFF;
        return op_stage_5b_table[second_op_code][current_state->stage_idx];
    } else if ((current_state->op_code & 0xFF00) == 0x9200) {
        uint8_t second_op_code = current_state->op_code & 0xFF;
        return op_stage_lnot_table[second_op_code][current_state->stage_idx];
    } else if ((current_state->op_code & 0xFF00) == 0xFE00) {
        uint8_t second_op_code = current_state->op_code & 0xFF;
        return op_stage_custom[second_op_code][current_state->stage_idx];
    }

    return op_stage_table[current_state->op_code][current_state->stage_idx];
}

void state_stack_create(uint16_t op_code, bool evaluation)
{
    current_state = (parse_state_t *)mempool_alloc(&state_stack_mempool, sizeof(parse_state_t));
    current_state->op_code = op_code;
    current_state->stage_idx = 0;
    current_state->evaluation = evaluation;
    current_state->node_start = scanner.current - 1;
    if ((op_code & 0x5B00) == 0x5B00) {
        current_state->node_start = scanner.current - 2;
    }
}

void state_stack_push(uint16_t op_code, bool evaluation)
{
    parse_state_t *reserved_state = current_state;

    state_stack_create(op_code, evaluation);
    current_state->parent = reserved_state;
    current_state->node = current_state->parent->node; // used for looking up namespace nodes
}

void state_stack_add_argument(aml_data_t argument)
{
    /* sddf_dprintf("add argument(%u): {0x%lx, %u, %u} to op 0x%04x\n", current_state->num_args, argument.value, argument.type, argument.length, current_state->op_code); */
    current_state->arguments[current_state->num_args].value = argument.value;
    current_state->arguments[current_state->num_args].type = argument.type;
    current_state->arguments[current_state->num_args].length = argument.length;
    current_state->num_args++;
}

void write_to_buffer(uint64_t buf_addr, uint64_t value, uint8_t bytes)
{
    sddf_dprintf("update FIELD(%u bytes) to 0x%lx at 0x%lx\n",
                 bytes,
                 value,
                 buf_addr);

    uint8_t *buffer = (uint8_t *)buf_addr;
    while (bytes--) {
        *buffer = value & 0xFF;
        value = value >> 8;
        buffer++;
    }
}

void store_op_evaluation()
{
    assert(current_state->num_args == 2);
    assert(current_state->arguments[1].type == DATA_OBJ_NODE);
    aml_namespace_node_t *target_node = (aml_namespace_node_t *)current_state->arguments[1].value;
    if (target_node) {
        // TODO: distinguish bitIndex and ByteIndex
        switch (target_node->op_code) {
            case CREATE_BIT_FIELD_OP: {
                sddf_dprintf("update BIT_FIELD %s to 0x%lx at 0x%lx\n",
                             target_node->name,
                             current_state->arguments[0].value,
                             target_node->data.value);
                uint8_t *buf_to_update = (uint8_t *)target_node->data.value;
                // bitOffset in byte is stored in data.length
                uint8_t bit_value = 0;
                if (current_state->arguments[0].value) {
                    bit_value = 0xFF;
                } else {
                    bit_value = ~(1 << (target_node->data.length % 8));
                }
                // TODO: improve this
                *buf_to_update = (*buf_to_update) & bit_value;
                break;
            }
            case CREATE_BYTE_FIELD_OP: {
                write_to_buffer(target_node->data.value, current_state->arguments[0].value, 1);
                break;
            }
            case CREATE_WORD_FIELD_OP: {
                write_to_buffer(target_node->data.value, current_state->arguments[0].value, 2);
                break;
            }
            case CREATE_DWORD_FIELD_OP: {
                write_to_buffer(target_node->data.value, current_state->arguments[0].value, 4);
                break;
            }
            case CREATE_QWORD_FIELD_OP: {
                write_to_buffer(target_node->data.value, current_state->arguments[0].value, 8);
                break;
            }
            default: {
                target_node->data = current_state->arguments[0];
                target_node->evaluated = true;
                sddf_dprintf("save value %lu to node\n", target_node->data.value);
            }
        }
    } else {
        sddf_dprintf("target node is invalid\n");
    }
}

void state_stack_update();
void state_stack_pop()
{
    aml_data_t ret_data;
    ret_data.type = DATA_OBJ_QWORD;
    if (current_state && current_state->num_args > 0) {
        ret_data = current_state->arguments[0];
    }

    if (current_state && current_state->evaluation) {
        switch (current_state->op_code) {
            case STORE_OP: {
                store_op_evaluation();
                break;
            }
            case LEQUAL_OP: {
                assert(current_state->num_args == 2);
                sddf_dprintf("Equal: %lu == %lu\n", current_state->arguments[0].value, current_state->arguments[1].value);
                ret_data.value = current_state->arguments[0].value == current_state->arguments[1].value;
                break;
            }
            case LNOT_EQUAL_OP: {
                assert(current_state->num_args == 2);
                sddf_dprintf("Equal: %lu != %lu\n", current_state->arguments[0].value, current_state->arguments[1].value);
                ret_data.value = current_state->arguments[0].value != current_state->arguments[1].value;
                break;
            }
            case LLESS_EQUAL_OP: {
                assert(current_state->num_args == 2);
                sddf_dprintf("Equal: %lu <= %lu\n", current_state->arguments[0].value, current_state->arguments[1].value);
                ret_data.value = current_state->arguments[0].value <= current_state->arguments[1].value;
                break;
            }
            case LGREATER_EQUAL_OP: {
                assert(current_state->num_args == 2);
                sddf_dprintf("Equal: %lu >= %lu\n", current_state->arguments[0].value, current_state->arguments[1].value);
                ret_data.value = current_state->arguments[0].value >= current_state->arguments[1].value;
                break;
            }
            case AND_OP: {
                assert(current_state->num_args == 3);
                assert(current_state->arguments[2].type == DATA_OBJ_NODE);
                ret_data.value = current_state->arguments[0].value & current_state->arguments[1].value;
                sddf_dprintf("and: 0x%lx & 0x%lx = 0x%lx\n", current_state->arguments[0].value, current_state->arguments[1].value, ret_data.value);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2].value;
                if (supername_node) {
                    supername_node->data = ret_data;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->data.value, supername_node->name);
                }
                break;
            }
            case ADD_OP: {
                assert(current_state->num_args == 3);
                assert(current_state->arguments[2].type == DATA_OBJ_NODE);
                ret_data.value = current_state->arguments[0].value + current_state->arguments[1].value;
                sddf_dprintf("add: 0x%lx + 0x%lx = 0x%lx\n", current_state->arguments[0].value, current_state->arguments[1].value, ret_data.value);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2].value;
                if (supername_node) {
                    supername_node->data = ret_data;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->data.value, supername_node->name);
                }
                break;
            }
            case SUBTRACT_OP: {
                assert(current_state->num_args == 3);
                assert(current_state->arguments[2].type == DATA_OBJ_NODE);
                ret_data.value = current_state->arguments[0].value - current_state->arguments[1].value;
                sddf_dprintf("subtract: 0x%lx - 0x%lx = 0x%lx\n", current_state->arguments[0].value, current_state->arguments[1].value, ret_data.value);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2].value;
                if (supername_node) {
                    supername_node->data = ret_data;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->data.value, supername_node->name);
                }
                break;
            }
            case SHIFT_LEFT_OP: {
                assert(current_state->num_args == 3);
                assert(current_state->arguments[2].type == DATA_OBJ_NODE);
                sddf_dprintf("argument0: 0x%lx, argument1: 0x%lx\n", current_state->arguments[0].value, current_state->arguments[1].value);
                ret_data.value = (current_state->arguments[0].value) << (current_state->arguments[1].value);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2].value;
                if (supername_node) {
                    supername_node->data.value = ret_data.value;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->data.value, supername_node->name);
                }
                break;
            }
            case SHIFT_RIGHT_OP: {
                assert(current_state->num_args == 3);
                assert(current_state->arguments[2].type == DATA_OBJ_NODE);
                ret_data.value = (current_state->arguments[0].value) >> (current_state->arguments[1].value);
                sddf_dprintf("argument0: 0x%lx, argument1: 0x%lx, ret_val: 0x%lx\n", current_state->arguments[0].value, current_state->arguments[1].value, ret_data.value);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2].value;
                if (supername_node) {
                    supername_node->data.value = ret_data.value;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->data.value, supername_node->name);
                }
                break;
            }
            case BUFFER_PREFIX: {
                assert(current_state->num_args == 1);
                ret_data.value = (uint64_t)current_state->pkt_end - current_state->arguments[0].value;
                ret_data.type = DATA_OBJ_BUFFER;
                ret_data.length = current_state->arguments[0].value;
                sddf_dprintf("return buffer prefix: 0x%lx, len: 0x%x\n", ret_data.value, ret_data.length);
                break;
            }
            case PACKAGE_PREFIX: {
                assert(current_state->num_args == 1);
                ret_data.value = current_state->arguments[0].value;
                ret_data.length = (uint64_t)current_state->pkt_end - current_state->arguments[0].value;
                ret_data.type = DATA_OBJ_PACKAGE;
                sddf_dprintf("return package prefix: 0x%lx\n", ret_data.value);
                break;
            }
            case NAME_OP: {
                assert(current_state->num_args == 2);
                assert(current_state->arguments[0].type == DATA_OBJ_RET);
                sddf_dprintf("complete NameOp %s: addr: 0x%lx, ret_buf = %u\n", current_state->node->name, (uintptr_t)current_state->arguments[0].value, (uint32_t)current_state->arguments[2].value);
                // TODO: check ret_type
                aml_data_t *eval_ret = (aml_data_t *)current_state->arguments[0].value;
                *eval_ret = current_state->arguments[1];
                ret_data = current_state->arguments[1];
                if (current_state->node) {
                    current_state->node->data = current_state->arguments[1];
                    current_state->node->evaluated = true;
                }
                break;
            }
            case RETURN_OP: {
                assert(current_state->num_args == 1);
                sddf_dprintf("complete MethodOp: %s, ret_buf = 0x%lx\n", current_state->parent->node->name, (uint64_t)current_state->arguments[0].value);
                aml_data_t method_ret = current_state->arguments[0];
                while (current_state && current_state->op_code != METHOD_OP) {
                    parse_state_t *completed_state = current_state;
                    current_state = current_state->parent;
                    mempool_rc(&state_stack_mempool, (void *)completed_state, sizeof(parse_state_t));
                }
                if (current_state) {
                    aml_data_t *eval_ret = (aml_data_t *)current_state->arguments[0].value;
                    *eval_ret = method_ret;
                    current_state->stage_idx += 1; // MethodOp completes
                }
                break;
            }
            case PRT_PACKAGE: {
                assert(current_state->num_args == 5);
                assert(current_state->arguments[0].type == DATA_OBJ_RET);
                aml_prt_package_t *prt = (aml_prt_package_t *)current_state->arguments[0].value;
                prt->address = current_state->arguments[1];
                prt->pin = current_state->arguments[2];
                prt->source = current_state->arguments[3];
                prt->source_index = current_state->arguments[4];
                break;
            }
            case OP_REGION_OP: {
                assert(current_state->num_args == 4);
                assert(current_state->arguments[0].type == DATA_OBJ_RET);
                uint8_t region_space = current_state->arguments[1].value;
                uintptr_t region_offset = current_state->arguments[2].value;
                uint64_t region_length = current_state->arguments[3].value;
                assert(current_state->arguments[0].value % 8 == 0);
                aml_data_t *eval_ret = (aml_data_t *)current_state->arguments[0].value;

                uintptr_t field_register = region_offset;
                if (region_space == 0x00) {

                } else if (region_space == 0x02) {
                    aml_namespace_node_t *adr_node = find_namespace_node_by_name(current_state->node, acpi_str_adr);
                    // TODO: this might be 64-bit
                    uint64_t address;
                    aml_data_t addr_eval_ret = eval_namespace_node(adr_node, 0, NULL);
                    address = addr_eval_ret.value;
                    sddf_dprintf("address node name: %s, addr: 0x%lx\n", adr_node->name, address);

                    uint64_t bus;
                    aml_namespace_node_t *bbn_node = find_namespace_node_by_name(current_state->node, acpi_str_bbn);
                    aml_data_t bus_eval_ret = eval_namespace_node(bbn_node, 0, NULL);
                    bus = bus_eval_ret.value;
                    sddf_dprintf("bus node name: %s, bus: 0x%lx\n", bbn_node->name, bus);

                    // TODO: use of region_offset and region_length
                    sddf_dprintf("field_reg: 0x%lx, bus: 0x%lx, address: 0x%lx, region_offset: 0x%lx\n", field_register, bus, address, region_offset);
                    field_register = ecam_base_paddr + field_register + (bus << 20) + address;
                } else {
                    sddf_dprintf("Region space 0x%x is not implemneted\n", region_space);
                }

                sddf_dprintf("field_register: 0x%lx\n", field_register);
                eval_ret->value = field_register;
                eval_ret->length = region_length;
                ret_data = *eval_ret;

                /* sddf_dprintf("complete OpRegionOp: %s, ret_buf = %lu\n", current_state->node->name, eval_ret->value); */
                break;
            }
            case CREATE_BIT_FIELD_OP:
            case CREATE_BYTE_FIELD_OP:
            case CREATE_WORD_FIELD_OP:
            case CREATE_DWORD_FIELD_OP:
            case CREATE_QWORD_FIELD_OP: {
                assert(current_state->num_args == 2);
                assert(current_state->arguments[0].type == DATA_OBJ_BUFFER);
                aml_data_t field_buffer = current_state->arguments[0];
                uint64_t index = current_state->arguments[1].value;
                if (current_state->op_code == CREATE_BIT_FIELD_OP) {
                    // 2nd argument is bitIndex in CreateBitFieldOp
                    field_buffer.value = field_buffer.value + index / 8;
                    // use buffer_field.length as bit offset
                    field_buffer.length = index % 8;
                } else {
                    // 2nd argument is byteIndex
                    field_buffer.value = field_buffer.value + index;
                }
                current_state->node->data = field_buffer;
                current_state->node->evaluated = true;
                /* sddf_dprintf("CreateFieldOp: {0x%lx, %u, %u}, name: %s\n", field_buffer.value, field_buffer.type, field_buffer.length, current_state->node->name); */
                break;
            }
        }
    }

    // Update
    if ((current_state->parent == NULL || current_state->parent->node != current_state->node) && current_state->node && current_state->node->pkt_end == 0) {
        current_state->node->pkt_end = scanner.current;
        /* sddf_dprintf("save pkt_end 0x%lx to node %s\n", (uintptr_t)scanner.current, current_state->node->name); */
    }

    /* sddf_dprintf("Stack pop Op 0x%04x, current: 0x%lx, pkt_end: 0x%lx, parent: 0x%lx\n", current_state->op_code, (uintptr_t)scanner.current, (uintptr_t)current_state->pkt_end, (uintptr_t)current_state->parent); */
    parse_state_t *completed_state = current_state;
    current_state = current_state->parent;
    mempool_rc(&state_stack_mempool, (void *)completed_state, sizeof(parse_state_t));

    if (current_state != NULL) {
        parse_stage_t op_stage = get_op_stage();
        if (op_stage == TERM_INTEGER || op_stage == BUFFER_DATA || op_stage == DATA_OBJECT) {
            state_stack_add_argument(ret_data);
            /* sddf_dprintf("after argument adding: Op 0x%04x, idx: %u, current: 0x%lx, pkt_end: 0x%lx\n", current_state->op_code, current_state->stage_idx, (uintptr_t)scanner.current, (uintptr_t)current_state->pkt_end); */
            state_stack_update();
        }
    }

    if (current_state != NULL) {
        parse_stage_t op_stage = get_op_stage();
        if ((current_state->pkt_end && scanner.current >= current_state->pkt_end) || op_stage == COMPLETE) {
            /* sddf_dprintf("pop at end current: 0x%lx, pkt_end: 0x%lx\n", (uintptr_t)scanner.current, (uintptr_t)current_state->pkt_end); */
            state_stack_pop();
        }
    }
}

void state_stack_update()
{
    parse_stage_t op_stage = get_op_stage();
    if (!current_state->evaluation && (current_state->op_code == IF_OP || current_state->op_code == ELSE_OP) && op_stage == PKT_LEN) {
        // TODO: This should be removed once real-time value reading is implemented
        if (current_state->evaluation == false) {
            current_state->stage_idx = 4;
        }
    } else if (!current_state->evaluation && current_state->op_code == IF_OP && op_stage == TERM_INTEGER) {
        if (current_state->num_args == 1 && current_state->arguments[0].value == 0) {
            current_state->stage_idx += 2;
        }
    } else if (!current_state->evaluation && current_state->op_code == METHOD_OP && op_stage == OBJECT_NAME_STRING) {
        current_state->stage_idx += 3;
        scanner.current = current_state->pkt_end;
    } else if (current_state->evaluation && current_state->op_code == IF_OP && op_stage == TERM_INTEGER) {
        if (current_state->num_args == 1 && current_state->arguments[0].value == 0) {
            current_state->parent->if_condition = false;
            current_state->stage_idx += 2;
        } else {
            current_state->parent->if_condition = true;
        }
    } else if (current_state->evaluation && current_state->op_code == ELSE_OP && op_stage == PKT_LEN) {
        if (current_state->parent->if_condition) {
            sddf_dprintf("Skip Elseif to 0x%lx\n", (uintptr_t)current_state->pkt_end);
            current_state->stage_idx += 2;
        } else {
            current_state->stage_idx += 1;
        }
    } else if (current_state->op_code == BUFFER_PREFIX && op_stage == TERM_INTEGER) {
        /* sddf_dprintf("buffer pkt_start: 0x%lx, pkt_end: 0x%lx, buffer_size: 0x%lx\n", */
                     /* (uintptr_t)current_state->node->pkt_start, */
                     /* (uintptr_t)current_state->pkt_end, */
                     /* current_state->arguments[0].value); */
        current_state->stage_idx += 2;
    } else if (current_state->op_code == PACKAGE_PREFIX && op_stage == PKT_LEN) {
        aml_data_t package_start = {(uint64_t)scanner.current, DATA_OBJ_QWORD, 0};
        state_stack_add_argument(package_start);
        current_state->stage_idx += 1;
    } else if (op_stage != TERM_LIST) {
        current_state->stage_idx += 1;
    }

    /* sddf_dprintf("current op_code: 0x%04x, idx: %u, stage: %u, num_args: %u\n", current_state->op_code, current_state->stage_idx, get_op_stage(), current_state->num_args); */

    // Check if the Op has been completely parsed
    op_stage = get_op_stage();
    if (op_stage == COMPLETE) {
        if (current_state->pkt_end != 0) {
            scanner.current = current_state->pkt_end;
        }
        state_stack_pop();
    }
}

// ======================= AML Parser ====================

void set_scanner_to(uint8_t *start)
{
    scanner.current = start;
}

uint8_t advance() {
    scanner.current++;
    return scanner.current[-1];
}

// scanner.current should be at start of pktLength when invoked
// PktLength consists of LeadByte followed by variable-length bytes, see more in Section 20.2.4
uint8_t *get_pkt_end()
{
    uint8_t lead_byte = advance();
    uint8_t extra_bytes_len = lead_byte >> 6;

    // pktLength encoded in bits 5-0 if one byte long
    if (extra_bytes_len == 0) {
        return scanner.current + (lead_byte & 0x3F) - 1;
    }

    uint32_t pkt_len = (lead_byte & 0xF) + (advance() << 4);
    if (extra_bytes_len > 1) pkt_len += (advance() << 12);
    if (extra_bytes_len > 2) pkt_len += (advance() << 20);

    return scanner.current + pkt_len - extra_bytes_len - 1;
}

// See more in Section 20.2.2
void skip_name_string()
{
    uint8_t name_type = advance();

    if ((name_type >= 'A' && name_type < 'Z') || name_type == '_') {
        // Name Segment
        scanner.current += 3;
    } else if (name_type == '\\' || name_type == '^') {
        // Root Path
        skip_name_string();
    } else if (name_type == 0x2E) {
        // Dual Name Segment
        scanner.current += 8;
    } else if (name_type == 0x2F) {
        // Multiple Name Segment
        uint8_t seg_cnt = advance();
        scanner.current += (4 * seg_cnt);
    } else {
        scanner.current--;
    }
}

// Parse the compressed EISA ID to readable characters
// see 19.3.4 ASL Macros, EISAID
void read_eisa_id(aml_namespace_node_t *node, char *eisa_id_str)
{
    scanner.current = node->pkt_start + 1; // First byte for NAME_OP
    skip_name_string();

    uint8_t eisa_type = advance();

    if (eisa_type == DATA_OBJ_DWORD) {
        // Combine the first two bytes in little-endian
        uint16_t char_word = advance() << 8;
        char_word |= advance();

        // Extract the 3 characters
        // Bit mapping: 0-4 (Char 3), 5-9 (Char 2), 10-14 (Char 1)
        eisa_id_str[0] = (char)(((char_word >> 10) & 0x1F) + 0x40);
        eisa_id_str[1] = (char)(((char_word >> 5)  & 0x1F) + 0x40);
        eisa_id_str[2] = (char)((char_word & 0x1F) + 0x40);

        // Extract four Hex ID from the last two bytes
        uint8_t hex_hi = advance();
        eisa_id_str[3] = (char)(HEX_TO_CHAR(hex_hi >> 4));
        eisa_id_str[4] = (char)(HEX_TO_CHAR(hex_hi & 0xF));
        uint8_t hex_lo = advance();
        eisa_id_str[5] = (char)(HEX_TO_CHAR(hex_lo >> 4));
        eisa_id_str[6] = (char)(HEX_TO_CHAR(hex_lo & 0xF));
        eisa_id_str[7] = '\0';
    } else if (eisa_type == DATA_OBJ_STRING){
        char c;
        uint8_t i = 0;
        while ((c = advance())) {
            eisa_id_str[i] = c;
            i++;
        }
        eisa_id_str[i] = '\0';
    }
}

void read_name_segment(char *name_segment)
{
    name_segment[0] = (char)advance();
    name_segment[1] = (char)advance();
    name_segment[2] = (char)advance();
    name_segment[3] = (char)advance();
    name_segment[4] = '\0';
}

aml_namespace_node_t *find_node_by_name_string(aml_namespace_node_t *parent_node, uint8_t left_num_segments)
{
    char name_segment[5];
    uint8_t name_type = advance();
    aml_namespace_node_t *node = NULL;

    /* sddf_dprintf("name_type: 0x%x, current: 0x%lx, parent: %s\n", name_type, (uintptr_t)scanner.current, parent_node->name); */
    if (name_type == 0x00) {
        /* sddf_dprintf("Null Name\n"); */
        return NULL;
    }

    if (name_type >= LOCAL0_OP && name_type <= LOCAL7_OP) {
        scanner.current--;
        aml_namespace_node_t *local_variable = find_local_variable_in_namespace(parent_node, name_type);
        if (local_variable) {
            return local_variable;
        }

        return namespace_insert_child_node(parent_node, NULL, name_type);
    }

    if (name_type >= ARG0_OP && name_type <= ARG6_OP) {
        scanner.current--;
        aml_namespace_node_t *local_variable = find_local_variable_in_namespace(parent_node, name_type);
        if (local_variable) {
            return local_variable;
        }

        sddf_dprintf("[Error] node ARG%u is not found\n", name_type - ARG0_OP);
        return NULL;
    }

    if ((name_type >= 'A' && name_type < 'Z') || name_type == '_') {
        // Name Segment
        scanner.current--;
        read_name_segment(name_segment);
        node = find_namespace_node_by_name(current_state->node, name_segment);
        left_num_segments--;
        /* sddf_dprintf("  node: 0x%lx, current: 0x%lx, segment: %s, parent: %s\n", (uintptr_t)node, (uintptr_t)scanner.current, name_segment, parent_node->name); */
    } else if (name_type == '\\') {
        // Root Path
        node = &namespace_root;
    } else if (name_type == 0x2E) {
        // Dual Name Segment
        left_num_segments = 2;
        node = parent_node;
    } else if (name_type == 0x2F) {
        // Multiple Name Segment
        uint8_t seg_cnt = advance();
        left_num_segments = seg_cnt;
        node = parent_node;
    } else {
        sddf_dprintf("Not a NameString at 0x%lx\n", (uintptr_t)scanner.current);
        scanner.current--;
        return NULL;
    }

    if (node == NULL) {
        return NULL;
    }

    if (left_num_segments > 0) {
        /* sddf_dprintf("  Parent: %s, Name segment: %s, left_num_segments: %u\n", node->name, name_segment, left_num_segments); */
        return find_node_by_name_string(node, left_num_segments);
    }

    if (node->op_code == NAME_OP || node->op_code == METHOD_OP || node->op_code == DEVICE_OP
        || node->op_code == OP_REGION_OP || node->op_code == FIELD_OP || node->op_code == CREATE_DWORD_FIELD_OP
        || node->op_code == CREATE_QWORD_FIELD_OP || node->op_code == CREATE_WORD_FIELD_OP) {
        return node;
    } else {
        sddf_dprintf("Object \'%s\' has invalid OpCode: 0x%x, try parsing the following name segment at 0x%lx\n", node->name, node->op_code, (uintptr_t)scanner.current);
        return find_node_by_name_string(node, 1);
    }

    return NULL;
}

uint8_t *get_data_end()
{
    uint8_t first_byte = advance();
    switch (first_byte) {
        case DATA_OBJ_ZERO:
        case DATA_OBJ_ONE:
            return scanner.current;
        case DATA_OBJ_BYTE:
            return scanner.current + 1;
        case DATA_OBJ_WORD:
            return scanner.current + 2;
        case DATA_OBJ_DWORD:
            return scanner.current + 4;
        case DATA_OBJ_QWORD:
            return scanner.current + 8;
        case DATA_OBJ_STRING: {
            while (advance());
            return scanner.current;
        case DATA_OBJ_BUFFER:
            return get_pkt_end();
        case DATA_OBJ_PACKAGE:
            return get_pkt_end();
        default:
            sddf_dprintf("Unkown prefix: 0x%x\n", first_byte);
        }
    }
    return 0;
}

aml_namespace_node_t *make_namespace_node(aml_namespace_node_t *namespace, uint16_t op_code)
{
    uint8_t name_type = advance();

    if (name_type == '\\') {
        namespace = &namespace_root;
        name_type = advance();
    }

    if (name_type == '^') {
        namespace = namespace->parent;
        name_type = advance();
    }

    if (name_type == 0x00) {
        return namespace;
    }

    // Local variable [Local0Op, Local7Op] or ARGs [ARG0, ARG6]
    if ((op_code >= LOCAL0_OP && op_code <= LOCAL7_OP) || (op_code >= ARG0_OP && op_code <= ARG6_OP)) {
        scanner.current--;
        aml_namespace_node_t *local_variable = find_local_variable_in_namespace(namespace, op_code);
        if (local_variable) {
            return local_variable;
        }
        return namespace_insert_child_node(namespace, NULL, op_code);
    }

    if ((name_type >= 'A' && name_type <= 'Z') || name_type == '_') {
        scanner.current--;
        char name_segment[5];
        read_name_segment(name_segment);
        aml_namespace_node_t *existing_node = find_child_node_by_name(namespace, name_segment);
        if (existing_node) {
            return existing_node;
        }

        return namespace_insert_child_node(namespace, name_segment, op_code);
    }

    uint8_t name_segment_cnt = 0;
    if (name_type == 0x2E) {
        name_segment_cnt = 2;
    } else if (name_type == 0x2F) {
        name_segment_cnt = advance();
    } else {
        sddf_dprintf("[Error] invalid encoding \'0x%02x\' for expected NameString at 0x%lx\n", name_type, (uintptr_t)scanner.current);
        return NULL;
    }

    while (--name_segment_cnt) {
        namespace = make_namespace_node(namespace, NULL_OP);
    }

    return make_namespace_node(namespace, op_code);
}

void parse_field_list()
{
    assert(current_state->arguments[0].type == DATA_OBJ_BYTE);
    uint8_t field_flags = current_state->arguments[0].value;
    // AccessType: bit 0-3 in FieldFlags
    uint8_t access_type = field_flags & 0xF;
    // Save 4-bit AccessType as data type of FieldOp to be used as alignment size
    aml_data_type_t access_data_type = DATA_OBJ_ZERO;
    switch (access_type) {
        case 0: { access_data_type = DATA_OBJ_ZERO; break; } // DATA_OBJ_ZERO indicates AnyAcc
        case 1: { access_data_type = DATA_OBJ_BYTE; break; }
        case 2: { access_data_type = DATA_OBJ_WORD; break; }
        case 3: { access_data_type = DATA_OBJ_DWORD; break; }
        case 4: { access_data_type = DATA_OBJ_QWORD; break; }
        case 5: { access_data_type = DATA_OBJ_BUFFER; break; }
        default: {
            sddf_dprintf("[Error] Unsupported AccessType: 0x%x\n", access_type);
        }
    }

    uint32_t bit_offset = 0;
    while (scanner.current < current_state->pkt_end) {
        uint8_t byte = advance();
        if ((byte >= 'A' && byte <= 'Z') || byte == '_') {
            scanner.current--;
            // Create FieldOps as direct Children of OpRegionOp
            aml_namespace_node_t *field_node = make_namespace_node(current_state->node, FIELD_OP);
            uint8_t *field_element_start = scanner.current;
            uint32_t bit_width = get_pkt_end() - field_element_start;
            // Save "| 56-bit offset | 8-bit width |" in data of FieldOp
            field_node->data.value = ((uint64_t)bit_offset << 8) | bit_width;
            field_node->data.type = access_data_type;
            /* sddf_dprintf("field name: %s, bit_width: %u, bit_offset: 0x%x\n", field_node->name, bit_width, bit_offset); */
            bit_offset += bit_width;
        } else if (byte == 0x00) {
            uint8_t *field_element_start = scanner.current;
            uint8_t *reserved_pkt_end = get_pkt_end();
            uint32_t padding_bits = (uint32_t)(reserved_pkt_end - field_element_start);
            bit_offset += padding_bits;
            /* sddf_dprintf("Reserved: current: 0x%lx, reserved_pkt_end: 0x%lx, width: 0x%x\n", (uintptr_t)scanner.current, (uintptr_t)reserved_pkt_end, padding_bits); */
            /* sddf_dprintf("bit_offset: 0x%x\n", bit_offset); */
        } else if (byte == 0x01) {
            advance(); // Type
            advance(); // Attrib
            /* sddf_dprintf("Access field - type: 0x%x, attrib: 0x%x\n", type, attrib); */
        } else {
            sddf_dprintf("Error: unknown prefix - 0x%x\n", byte);
        }
    }
}

aml_data_t read_field_value(aml_namespace_node_t *field_node)
{
    sddf_dprintf("Try evaluating FieldOp: %s\n", field_node->name);

    // TODO: should be DWORD_DATA
    aml_data_t op_region = eval_namespace_node(field_node->parent, 0, NULL);
    sddf_dprintf("name: %s, ret_value: 0x%lx, op_code: 0x%x\n", field_node->parent->name, op_region.value, field_node->parent->op_code);

    // Decode bit_offset and bit_width from data of FieldOp
    uint64_t field_bit_offset = field_node->data.value >> 8;
    uint8_t field_bit_width = field_node->data.value & 0xFF;
    sddf_dprintf("Field offset: 0x%lx, bit_offset: 0x%lx, width: %u\n", field_bit_offset / 8, field_bit_offset % 8, field_bit_width);

    // Align the field address to a 1-byte boundary
    uintptr_t field_paddr = op_region.value + (field_bit_offset / 8);
    uint8_t bit_offset = field_bit_offset % 8;

    // TODO: replace this constant value with a macro;
    uintptr_t field_vaddr = 0x4000000 + PAGE_OFFSET(field_paddr);;
    map_memory_region(&post_boot_cnode, field_paddr, op_region.length, field_vaddr);

    uint64_t final_field_value = 0;
    uint8_t remaining_bit_width = field_bit_width;
    // TODO: BufferAcc?
    while (remaining_bit_width) {
        uint8_t bit_width_to_read = 0;
        uint64_t reg_val = 0;
        switch (field_node->data.type) {
            case DATA_OBJ_ZERO:
            case DATA_OBJ_BYTE: {
                bit_width_to_read = MIN(8 - bit_offset, remaining_bit_width);

                uint8_t *read_field_reg = (uint8_t *)field_vaddr;
                reg_val = (uint64_t)*read_field_reg;
                reg_val = READ_BITS(reg_val, bit_offset, bit_width_to_read);

                field_paddr += 1;
                field_vaddr += 1;
                break;
            }
            case DATA_OBJ_WORD: {
                // Adjust to 2-byte alignment
                bit_offset = bit_offset + (field_paddr % 2) * 8;
                field_paddr = ROUND_DOWN(field_paddr, 2);
                bit_width_to_read = MIN(2 * 8 - bit_offset, remaining_bit_width);

                uint16_t *read_field_reg = (uint16_t *)field_vaddr;
                reg_val = (uint64_t)*read_field_reg;
                reg_val = READ_BITS(reg_val, bit_offset, bit_width_to_read);

                field_paddr += 2;
                field_vaddr += 2;
                break;
            }
            case DATA_OBJ_DWORD: {
                // Adjust to 4-byte alignment
                bit_offset = bit_offset + (field_paddr % 4) * 8;
                field_paddr = ROUND_DOWN(field_paddr, 4);
                field_vaddr = ROUND_DOWN(field_vaddr, 4);
                bit_width_to_read = MIN(4 * 8 - bit_offset, remaining_bit_width);

                uint32_t *read_field_reg = (uint32_t *)field_vaddr;
                reg_val = (uint64_t)*read_field_reg;
                reg_val = READ_BITS(reg_val, bit_offset, bit_width_to_read);

                field_paddr += 4;
                field_vaddr += 4;
                break;
            }
            case DATA_OBJ_QWORD: {
                // Adjust to 8-byte alignment
                bit_offset = bit_offset + (field_paddr % 8) * 8;
                field_paddr = ROUND_DOWN(field_paddr, 8);
                field_vaddr = ROUND_DOWN(field_vaddr, 8);
                bit_width_to_read = MIN(8 * 8 - bit_offset, remaining_bit_width);

                uint64_t *read_field_reg = (uint64_t *)field_vaddr;
                reg_val = (uint64_t)*read_field_reg;
                reg_val = READ_BITS(reg_val, bit_offset, bit_width_to_read);

                field_paddr += 8;
                field_vaddr += 8;
                break;
            }
            default: {
                sddf_dprintf("[Error] Unsupported AccessType: 0x%x\n", field_node->data.type);
            }
        }

        sddf_dprintf("[READ] paddr: 0x%lx, bit_offset: %u, bit_width: %u, read: 0x%lx, final: 0x%lx\n", field_paddr, bit_offset, bit_width_to_read, reg_val, final_field_value);
        final_field_value = final_field_value + (reg_val << (field_bit_width - remaining_bit_width));
        bit_offset = 0; // no offset since round 2
        remaining_bit_width -= bit_width_to_read;
    }

    // Unmap the mapped region
    assert(cnode_untypeds_revoke(&post_boot_cnode) == seL4_NoError);

    sddf_dprintf("read field %s value: 0x%lx\n", field_node->name, final_field_value);

    aml_data_t field_data = {final_field_value, DATA_OBJ_QWORD, 0};
    return field_data;
}

void parse_namespace_node(bool evaluation)
{
    /* sddf_dprintf("Evaluation? %s\n", evaluation ? "true" : "false"); */

    uint16_t op_code = 0;
    uint8_t *namespace_end = current_state->pkt_end;
    /* sddf_dprintf("scanner.current: 0x%lx, end: 0x%lx\n", (uintptr_t)scanner.current, (uintptr_t)namespace_end); */

    while (scanner.current < namespace_end) {
        if (current_state == NULL) return;
        uint8_t op_stage = get_op_stage();
        if (op_stage == PKT_LEN) {
            current_state->pkt_end = get_pkt_end();
        /* } else if (!evaluation && op_stage == DATA_OBJECT) { */
        /*     scanner.current = get_data_end(); */
        } else if (op_stage == OBJECT_NAME_STRING) {
            aml_namespace_node_t *new_node = make_namespace_node(current_state->parent->node, current_state->op_code);
            current_state->node = new_node;

            if (new_node->op_code != OP_REGION_OP) {
                new_node->pkt_start = current_state->node_start;
                if (current_state->pkt_end != 0) {
                    new_node->pkt_end = current_state->pkt_end;
                }
            }
        } else if (op_stage == NAME_STRING) {
            if (evaluation) {
                sddf_dprintf("Need to read the value of node at 0x%lx, %s\n", (uintptr_t)scanner.current, current_state->node->name);
                aml_namespace_node_t *node = find_node_by_name_string(current_state->node, 1);
                aml_data_t argument = {(uint64_t)node, DATA_OBJ_NODE, 0};
                state_stack_add_argument(argument);
            } else {
                /* sddf_dprintf("Skip Name String\n"); */
                skip_name_string();
            }
        } else if (op_stage == FIELD_LIST) {
            parse_field_list();
        } else if (op_stage == BYTE_DATA) {
            aml_data_t argument = {advance(), DATA_OBJ_BYTE, 0};
            state_stack_add_argument(argument);
        } else if (op_stage == WORD_DATA) {
            uint16_t data = advance();
            data |= (advance() << 8);
            aml_data_t argument = {data, DATA_OBJ_WORD, 0};
            state_stack_add_argument(argument);
        } else if (op_stage == DWORD_DATA) {
            uint32_t data = advance();
            data |= ((uint32_t)advance() << 8);
            data |= ((uint32_t)advance() << 16);
            data |= ((uint32_t)advance() << 24);
            aml_data_t argument = {data, DATA_OBJ_DWORD, 0};
            state_stack_add_argument(argument);
        } else if (op_stage == QWORD_DATA) {
            uint64_t data = advance();
            data |= ((uint64_t)advance() << 8);
            data |= ((uint64_t)advance() << 16);
            data |= ((uint64_t)advance() << 24);
            data |= ((uint64_t)advance() << 32);
            data |= ((uint64_t)advance() << 40);
            data |= ((uint64_t)advance() << 48);
            data |= ((uint64_t)advance() << 56);
            aml_data_t argument = {data, DATA_OBJ_DWORD, 0};
            state_stack_add_argument(argument);
        } else if (op_stage == STRING_DATA) {
            while (advance());
        } else {
            op_code = op_code | advance();
            if (op_code == 0x5B || op_code == 0x92) {
                op_code = op_code << 8;
                continue;
            }

            switch (op_code) {
                case ZERO_OP: {
                    aml_data_t argument = {0, DATA_OBJ_ZERO, 0};
                    state_stack_add_argument(argument);
                    break;
                }
                case ONE_OP: {
                    aml_data_t argument = {1, DATA_OBJ_ONE, 0};
                    state_stack_add_argument(argument);
                    break;
                }
                case ARG0_OP:
                case ARG1_OP:
                case ARG2_OP:
                case ARG3_OP:
                case ARG4_OP:
                case ARG5_OP:
                case ARG6_OP: {
                    sddf_dprintf("name: %s\n", current_state->node->name);
                    aml_namespace_node_t *arg_node = find_local_variable_in_namespace(current_state->node, op_code);
                    if (arg_node == NULL) {
                        sddf_dprintf("[Error] No arg node found\n");
                    }
                    sddf_dprintf("Found arg 0x%lx\n", arg_node->data.value);
                    state_stack_add_argument(arg_node->data);
                    break;
                }
                case LOCAL0_OP:
                case LOCAL1_OP:
                case LOCAL2_OP:
                case LOCAL3_OP:
                case LOCAL4_OP:
                case LOCAL5_OP:
                case LOCAL6_OP:
                case LOCAL7_OP: {
                    aml_namespace_node_t *local_node = make_namespace_node(current_state->node, op_code);
                    sddf_dprintf("Local variable\n");
                    if (local_node && local_node->evaluated) {
                        state_stack_add_argument(local_node->data);
                    } else {
                        sddf_dprintf("Local%u is not found or evaluated\n", op_code - LOCAL0_OP);
                    }
                    break;
                }
                case BYTE_PREFIX:
                case WORD_PREFIX:
                case DWORD_PREFIX:
                case QWORD_PREFIX:
                case BUFFER_PREFIX:
                case PACKAGE_PREFIX:
                case STRING_PREFIX:
                case ADD_OP:
                case SUBTRACT_OP:
                case SHIFT_LEFT_OP:
                case SHIFT_RIGHT_OP:
                case AND_OP:
                case ALIAS_OP:
                case SCOPE_OP:
                case METHOD_OP:
                case NAME_OP:
                case MUTEX_OP:
                case EVENT_OP:
                case FIELD_OP:
                case INDEX_FIELD_OP:
                case DEREF_OF_OP:
                case INDEX_OP:
                case IF_OP:
                case ELSE_OP:
                case STORE_OP:
                case LEQUAL_OP:
                case OP_REGION_OP:
                case CREATE_FIELD_OP:
                case CREATE_BIT_FIELD_OP:
                case CREATE_BYTE_FIELD_OP:
                case CREATE_WORD_FIELD_OP:
                case CREATE_DWORD_FIELD_OP:
                case CREATE_QWORD_FIELD_OP:
                case LNOT_EQUAL_OP:
                case LLESS_EQUAL_OP:
                case LGREATER_EQUAL_OP:
                case POWER_RESOURCE_OP:
                case PROCESSOR_OP:
                case THERMAL_ZONE_OP:
                case DEVICE_OP:
                case RETURN_OP: {
                    if (evaluation) {
                        /* sddf_dprintf("stack push 0x%04x\n", op_code); */
                    }
                    state_stack_push(op_code, evaluation);
                    break;
                }
                default: {
                    scanner.current--;
                    if (evaluation) {
                        // Try looking up the object by name string by name string by name string by name string
                        aml_namespace_node_t *node = find_node_by_name_string(current_state->node, 1);
                        if (node) {
                            /* sddf_dprintf("Found node %s\n", node->name); */

                            aml_data_t eval_ret = eval_namespace_node(node, 0, NULL);
                            state_stack_add_argument(eval_ret);
                        } else {
                            sddf_dprintf("[Error] Op \'0x%04x\' is not implemented\n", op_code);
                        }
                    } else {
                        /* sddf_dprintf("skip_name_string, op_code: 0x%x at 0x%lx\n", op_code, (uintptr_t)scanner.current); */
                        skip_name_string();
                    }
                }
            }
        }

        state_stack_update();
        op_code = 0;
    }
}

void scan_namespace_tree(aml_namespace_node_t *namespace, uint8_t *namespace_end)
{
    state_stack_create(NULL_OP, false);
    current_state->node_start = scanner.current;
    current_state->pkt_end = namespace_end;
    current_state->node = namespace;

    parse_namespace_node(false);
}

aml_data_t eval_namespace_node(aml_namespace_node_t *node, uint8_t num_args, aml_data_t argv[])
{
    aml_data_t eval_ret;

    if (node->evaluated) {
        eval_ret = node->data;
        return eval_ret;
    }

    parse_state_t *recovery_state = current_state;
    uint8_t *recovery_location = scanner.current;

    if (node->op_code == FIELD_OP) {
        eval_ret = read_field_value(node);
        current_state = recovery_state;
        scanner.current = recovery_location;
        return eval_ret;
    }

    /* sddf_dprintf("Eval node %s, Op: 0x%x, end: 0x%lx\n", node->name, node->op_code, (uintptr_t)node->pkt_end); */

    state_stack_create(node->op_code, true);
    current_state->node = node;
    current_state->node_start = node->pkt_start;
    current_state->pkt_end = node->pkt_end;
    current_state->stage_idx = 0;

    aml_data_t ret_buf = {(uintptr_t)&eval_ret, DATA_OBJ_RET, 0};
    state_stack_add_argument(ret_buf); // First argument as address of return buffer

    if (node->op_code == METHOD_OP) {
        // redirect scanner to TERM_LIST
        scanner.current = node->pkt_start + 1;
        get_pkt_end();      // PKT_LEN
        skip_name_string(); // NAME STRING
        advance();          // METHOD_FLAGS
        current_state->stage_idx = 4;

        // Add ARGn Ops
        for (int i = 0; i < num_args; i++) {
            aml_namespace_node_t *arg_node = make_namespace_node(current_state->node, ARG0_OP + i);
            arg_node->data = argv[i];
        }
    } else if (node->op_code == NAME_OP) {
        // redirect scanner to TERM_LIST
        scanner.current = node->pkt_start + 1;
        skip_name_string(); // NAME STRING
        current_state->stage_idx = 2;
    } else if (node->op_code == OP_REGION_OP) {
        // redirect scanner to region_space
        scanner.current = node->pkt_start + 2;
        skip_name_string(); // NAME STRING
        current_state->stage_idx = 2;
    } else {
        /* sddf_dprintf("Evaluation of op 0x%04x is not implmented, return node\n", node->op_code); */
        state_stack_pop();
        eval_ret = (aml_data_t){(uintptr_t)node, DATA_OBJ_NODE, 0};
        current_state = recovery_state;
        scanner.current = recovery_location;
        return eval_ret;
    }

    parse_namespace_node(true);

    /* sddf_dprintf("Finish Eval node %s, Op: 0x%x\n", node->name, node->op_code); */
    current_state = recovery_state;
    scanner.current = recovery_location;

    return eval_ret;
}

void eval_data_object(aml_namespace_node_t *prt_node, aml_prt_package_t *prt, uint8_t *pkt_end)
{
    aml_data_t ret_buf = {(uintptr_t)prt, DATA_OBJ_RET, 0};

    // Make a PRT_PACJAGE, and extract PRT data
    state_stack_create(PRT_PACKAGE, true);
    current_state->node = prt_node;
    current_state->node_start = 0;
    current_state->pkt_end = pkt_end;
    current_state->stage_idx = 3;

    state_stack_add_argument(ret_buf); // First argument as address of return buffer

    parse_namespace_node(true);
}

void parse_prt_package(aml_namespace_node_t *prt_node, aml_data_t prt_data, uint32_t bridge_idx)
{
    // DefPackage := PackageOp PkgLength NumElements PackageElementList
    if (prt_data.type != DATA_OBJ_PACKAGE) {
        sddf_dprintf("[Error] not a package data given\n");
        return;
    }

    set_scanner_to((uint8_t *)prt_data.value);
    uint8_t *package_end = (uint8_t *)prt_data.value + prt_data.length;
    pci_bridge_t *pci_bridge_resource = &pci_resources->bridges[pci_resources->num_bridges];

    uint8_t num_elements = advance();
    sddf_dprintf("num_elements: %u\n", num_elements);

    while (scanner.current < package_end) {
        // Check if element is also Package Object
        if (advance() != PACKAGE_PREFIX) return;

        uint8_t *element_pkt_end = get_pkt_end();
        uint32_t element_num_elements = advance();

        // Check if num of elements is 4
        if (element_num_elements != 4) return;

        pci_prt_t *pci_prt = &pci_bridge_resource->prt_entries[pci_bridge_resource->num_prt_entries];
        aml_prt_package_t prt_package;
        eval_data_object(prt_node, &prt_package, element_pkt_end);

        /* sddf_dprintf("==========\n"); */
        /* sddf_dprintf("address: 0x%lx, data_type: 0x%x\n", prt_package.address.value, prt_package.address.type); */
        /* sddf_dprintf("pin: 0x%lx, data_type: 0x%x\n", prt_package.pin.value, prt_package.pin.type); */
        /* sddf_dprintf("source: 0x%lx, data_type: 0x%x\n", prt_package.source.value, prt_package.source.type); */
        /* sddf_dprintf("sourceIndex: 0x%lx, data_type: 0x%x\n", prt_package.source_index.value, prt_package.source_index.type); */
        pci_prt->address = (uint32_t)prt_package.address.value;
        pci_prt->pin = (uint32_t)prt_package.pin.value;
        if (prt_package.source.type == DATA_OBJ_NODE) {
            aml_namespace_node_t *gsi_node = (aml_namespace_node_t *)prt_package.source.value;
            aml_namespace_node_t *crs_node = find_child_node_by_name(gsi_node, test_aml_str_crs);
            aml_data_t gsi_crs = eval_namespace_node(crs_node, 0, NULL);
            assert(gsi_crs.type == DATA_OBJ_BUFFER);
            uint8_t *irq_descriptor = (uint8_t *)gsi_crs.value;
            assert(irq_descriptor[0] == EXTENDED_IRQ_DESCRIPTOR);
            uint32_t gsi = 0;
            gsi |= (uint32_t)irq_descriptor[5] << 0;
            gsi |= (uint32_t)irq_descriptor[6] << 8;
            gsi |= (uint32_t)irq_descriptor[7] << 16;
            gsi |= (uint32_t)irq_descriptor[8] << 24;
            pci_prt->gsi = gsi;
            // TODO: edge/level, assumes there is only one IRQ for now
        } else {
            pci_prt->gsi = (uint32_t)prt_package.source_index.value;
        }
        pci_bridge_resource->num_prt_entries++;
        sddf_dprintf("{ address: 0x%X, pin: 0x%x, gsi: 0x%x}\n", pci_prt->address, pci_prt->pin, pci_prt->gsi);
    }
}
