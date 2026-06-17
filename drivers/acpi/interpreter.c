#include "acpi.h"
// =========================== Refactor =========================

const char acpi_str_adr[] = {'_', 'A', 'D', 'R', 0};  // Address
const char acpi_str_bbn[] = {'_', 'B', 'B', 'N', 0};  // BIOS Bus Number

typedef enum {
    INIT = 0,
    PKT_LEN,
    OBJECT_NAME_STRING, // Name String used for creating objects
    NAME_STRING,        // Name String referring to other objects
    TERM_ARG,
    TERM_LIST,
    TERM_INTEGER,
    TERM_BUFFER,
    FIELD_LIST,
    BYTE_INDEX,
    BUFFER,
    BYTE_DATA,
    WORD_DATA,
    DWORD_DATA,
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
    [CREATE_WORD_FIELD_OP] = { INIT, NAME_STRING, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_BIT_FIELD_OP] = { INIT, NAME_STRING, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_BYTE_FIELD_OP] = { INIT, NAME_STRING, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [CREATE_DWORD_FIELD_OP] = { INIT, NAME_STRING, TERM_INTEGER, OBJECT_NAME_STRING, COMPLETE },
    [LEQUAL_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, COMPLETE },
    [ADD_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [SUBTRACT_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [SHIFT_LEFT_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [SHIFT_RIGHT_OP] = { INIT, TERM_INTEGER, TERM_INTEGER, NAME_STRING, COMPLETE },
    [BYTE_PREFIX] = { INIT, BYTE_DATA, COMPLETE },
    [WORD_PREFIX] = { INIT, WORD_DATA, COMPLETE },
    [DWORD_PREFIX] = { INIT, DWORD_DATA, COMPLETE },
};

parse_stage_t op_stage_5b_table[MAX_OPCODE][MAX_OP_STAGES] = {
    [FIELD_OP & 0xFF] = { INIT, PKT_LEN, OBJECT_NAME_STRING, BYTE_DATA, FIELD_LIST, COMPLETE},
    [INDEX_FIELD_OP & 0xFF] = { INIT, PKT_LEN, COMPLETE},
    [OP_REGION_OP & 0xFF] = { INIT, OBJECT_NAME_STRING, BYTE_DATA, TERM_INTEGER, TERM_INTEGER, COMPLETE},
    [DEVICE_OP & 0xFF] = { INIT, PKT_LEN, OBJECT_NAME_STRING, TERM_LIST, COMPLETE },
    [MUTEX_OP & 0xFF] = { INIT, NAME_STRING, BYTE_DATA, COMPLETE },
    [POWER_RESOURCE_OP & 0xFF] = { INIT, PKT_LEN, NAME_STRING, BYTE_DATA, WORD_DATA, TERM_LIST, COMPLETE },
    [PROCESSOR_OP & 0xFF] = { INIT, PKT_LEN, COMPLETE },
};

typedef struct parse_state {
    struct parse_state *parent;
    uint8_t *node_start;
    uint8_t *pkt_end;
    aml_namespace_node_t *node;
    uint16_t op_code;
    uint8_t stage_idx;
    uint8_t num_args;
    uintptr_t arguments[10];
    bool evaluation;
} parse_state_t;

parse_state_t *current_state;

mempool_t state_stack_mempool = {
    .start = (void *)0x50000000,
    .next = (void *)0x50000000,
    .end = (void *)0x50010000,
};

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
        /* if (current_state && current_state->evaluation) { */
            /* sddf_dprintf("    parent: %s, node: %s, target: %s\n", node->name, child->name, name_segment); */
        /* } */
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
    aml_namespace_node_t *parent = node->parent;
    while (parent) {
        if (current_state && current_state->evaluation) {
            sddf_dprintf("  look for %s under parent %s\n", name_segment, parent->name);
        }
        aml_namespace_node_t *target = find_child_node_by_name(parent, name_segment);
        if (current_state && current_state->evaluation) {
            sddf_dprintf("  Done look for %s under parent %s\n", name_segment, parent->name);
        }
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
        sddf_dprintf("Create a type 0x%02X object: %s at 0x%lx, parent: %s\n", op_code, name_segment, (uintptr_t)scanner.current, namespace->name);
    } else {
        sddf_dprintf("Create a type 0x%02X object\n", op_code);
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

    if ((current_state->op_code & 0x5B00) == 0x5B00) {
        uint8_t second_op_code = current_state->op_code & 0xFF;
        return op_stage_5b_table[second_op_code][current_state->stage_idx];
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

void state_stack_add_argument(uintptr_t argument)
{
    sddf_dprintf("add argument(%u): 0x%lx to op 0x%04x\n", current_state->num_args, argument, current_state->op_code);
    current_state->arguments[current_state->num_args] = argument;
    current_state->num_args++;
}

void state_stack_update();
void state_stack_pop()
{
    uintptr_t ret_val = 0;
    if (current_state->num_args > 0) {
        ret_val = current_state->arguments[0];
    }

    if (current_state->evaluation) {
        switch (current_state->op_code) {
            case STORE_OP: {
                assert(current_state->num_args == 2);
                aml_namespace_node_t *target_node = (aml_namespace_node_t *)current_state->arguments[1];
                if (target_node) {
                    target_node->value = current_state->arguments[0];
                    target_node->evaluated = true;
                    sddf_dprintf("save value %lu to node\n", target_node->value);
                } else {
                    sddf_dprintf("target node is invalid\n");
                }
                break;
            }
            case LEQUAL_OP: {
                assert(current_state->num_args == 2);
                sddf_dprintf("Equal: %lu == %lu\n", current_state->arguments[0], current_state->arguments[1]);
                ret_val = current_state->arguments[0] == current_state->arguments[1];
                break;
            }
            case ADD_OP: {
                assert(current_state->num_args == 3);
                ret_val = current_state->arguments[0] + current_state->arguments[1];
                sddf_dprintf("subtract: 0x%lx - 0x%lx = 0x%lx\n", current_state->arguments[0], current_state->arguments[1], ret_val);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2];
                if (supername_node) {
                    supername_node->value = ret_val;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->value, supername_node->name);
                }
                break;
            }
            case SUBTRACT_OP: {
                assert(current_state->num_args == 3);
                ret_val = current_state->arguments[0] - current_state->arguments[1];
                sddf_dprintf("subtract: 0x%lx - 0x%lx = 0x%lx\n", current_state->arguments[0], current_state->arguments[1], ret_val);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2];
                if (supername_node) {
                    supername_node->value = ret_val;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->value, supername_node->name);
                }
                break;
            }
            case SHIFT_LEFT_OP: {
                assert(current_state->num_args == 3);
                sddf_dprintf("argument0: 0x%lx, argument1: 0x%lx\n", current_state->arguments[0], current_state->arguments[1]);
                ret_val = (current_state->arguments[0]) << (current_state->arguments[1]);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2];
                if (supername_node) {
                    supername_node->value = ret_val;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->value, supername_node->name);
                }
                break;
            }
            case SHIFT_RIGHT_OP: {
                assert(current_state->num_args == 3);
                ret_val = (current_state->arguments[0]) >> (current_state->arguments[1]);
                sddf_dprintf("argument0: 0x%lx, argument1: 0x%lx, ret_val: 0x%lx\n", current_state->arguments[0], current_state->arguments[1], ret_val);
                aml_namespace_node_t *supername_node = (aml_namespace_node_t *)current_state->arguments[2];
                if (supername_node) {
                    supername_node->value = ret_val;
                    supername_node->evaluated = true;
                    sddf_dprintf("save value %lu to node %s\n", supername_node->value, supername_node->name);
                }
                break;
            }
            case NAME_OP: {
                assert(current_state->num_args == 3);
                sddf_dprintf("complete NameOp: %s, addr: 0x%lx, ret_buf = %u\n", current_state->node->name, (uintptr_t)current_state->arguments[0], (uint32_t)current_state->arguments[2]);
                // TODO: no only uint32_t
                uint64_t *ret_buf = (uint32_t *)current_state->arguments[0];
                *ret_buf = (uint32_t)current_state->arguments[2];
                ret_val = *ret_buf;
                current_state->node->value = current_state->arguments[2];
                current_state->node->evaluated = true;
                break;
            }
            case RETURN_OP: {
                sddf_dprintf("complete MethodOp: %s, addr: 0x%lx, ret_buf = %u\n", current_state->parent->node->name, (uintptr_t)current_state->parent->arguments[0], (uint32_t)current_state->arguments[0]);
                uint64_t *ret_buf = (uint32_t *)current_state->parent->arguments[0];
                *ret_buf = (uint32_t)current_state->arguments[0];
                current_state->parent->stage_idx += 1; // MethodOp completes
                break;
            }
            case OP_REGION_OP: {
                uint8_t region_space = current_state->arguments[2];
                uintptr_t region_offset = current_state->arguments[3];
                // uint64_t region_length = current_state->arguments[4]; seems useless here, so ignore it
                assert(current_state->arguments[0] % 8 == 0);
                uintptr_t *ret_buf = (uintptr_t *)current_state->arguments[0];

                uintptr_t field_register = region_offset;
                if (region_space == 0x00) {

                } else if (region_space == 0x02) {
                    aml_namespace_node_t *adr_node = find_namespace_node_by_name(current_state->node, acpi_str_adr);
                    // TODO: this might be 64-bit
                    uint64_t address;
                    eval_namespace_node(adr_node, (uintptr_t)&address, WORD_DATA, 0, NULL);
                    sddf_dprintf("address node name: %s, addr: 0x%lx, ret_buf: %u\n", adr_node->name, (uintptr_t)&address, address);

                    uint64_t bus;
                    aml_namespace_node_t *bbn_node = find_namespace_node_by_name(current_state->node, acpi_str_bbn);
                    eval_namespace_node(bbn_node, (uintptr_t)&bus, WORD_DATA, 0, NULL);
                    sddf_dprintf("bus node name: %s, addr: 0x%lx, ret_buf: %u\n", bbn_node->name, (uintptr_t)&bus, bus);

                    // TODO: fix this hard-coded value
                    uintptr_t ecam_base_vaddr = 0x20000000;
                    // TODO: use of region_offset and region_length
                    sddf_dprintf("field_reg: 0x%lx, bus: 0x%lx, address: 0x%lx\n", field_register, bus, address);
                    field_register = field_register + ecam_base_vaddr + (bus << 20) + address;
                } else {
                    sddf_dprintf("Region space 0x%x is not implemneted\n", region_space);
                }

                sddf_dprintf("field_register: 0x%lx\n", field_register);
                *ret_buf = field_register;
                ret_val = *ret_buf;

                sddf_dprintf("complete OpRegionOp: %s, ret_buf = %u\n", current_state->node->name, *ret_buf);
                break;
            }
        }
    }

    if (current_state->node->pkt_end == 0) {
        current_state->node->pkt_end = scanner.current;
    }

    sddf_dprintf("Stack pop Op 0x%04x, current: 0x%lx, pkt_end: 0x%lx, parent: 0x%lx\n", current_state->op_code, (uintptr_t)scanner.current, (uintptr_t)current_state->pkt_end, (uintptr_t)current_state->parent);
    parse_state_t *completed_state = current_state;
    current_state = current_state->parent;
    mempool_rc(&state_stack_mempool, (void *)completed_state, sizeof(parse_state_t));

    if (current_state != NULL) {
        parse_stage_t op_stage = get_op_stage();
        if (op_stage == TERM_INTEGER || op_stage == TERM_BUFFER || op_stage == DATA_OBJECT) {
            state_stack_add_argument(ret_val);
            sddf_dprintf("after argument adding: Op 0x%04x, idx: %u, current: 0x%lx, pkt_end: 0x%lx, ret_val: 0x%lx\n", current_state->op_code, current_state->stage_idx, (uintptr_t)scanner.current, (uintptr_t)current_state->pkt_end, ret_val);
            state_stack_update();
            sddf_dprintf("finish update\n");
        }
    }

    if (current_state != NULL) {
        parse_stage_t op_stage = get_op_stage();
        if ((current_state->pkt_end && scanner.current >= current_state->pkt_end) || op_stage == COMPLETE) {
            sddf_dprintf("current: 0x%lx, pkt_end: 0x%lx\n", (uintptr_t)scanner.current, (uintptr_t)current_state->pkt_end);
            state_stack_pop();
            sddf_dprintf("finish pop\n");
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
        if (current_state->num_args == 1 && current_state->arguments[0] == 0) {
            current_state->stage_idx += 2;
        }
    } else if (!current_state->evaluation && current_state->op_code == METHOD_OP && op_stage == OBJECT_NAME_STRING) {
        current_state->stage_idx += 3;
        scanner.current = current_state->pkt_end;
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

    sddf_dprintf("name_type: 0x%x, current: 0x%lx\n", name_type, (uintptr_t)scanner.current);
    if (name_type == 0x00) {
        sddf_dprintf("Null Name\n");
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
        sddf_dprintf("  node: 0x%lx, current: 0x%lx, segment: %s, parent: %s\n", (uintptr_t)node, (uintptr_t)scanner.current, name_segment, parent_node->name);
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
        sddf_dprintf("  Parent: %s, Name segment: %s, left_num_segments: %u\n", node->name, name_segment, left_num_segments);
        return find_node_by_name_string(node, left_num_segments);
    }

    if (node->op_code == NAME_OP || node->op_code == METHOD_OP || node->op_code == DEVICE_OP || node->op_code == OP_REGION_OP || node->op_code == FIELD_OP) {
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
            uint32_t i = 0;
            while (advance());
            return scanner.current + i;
        case DATA_OBJ_BUFFER:
            return get_pkt_end();
        case DATA_OBJ_PACKAGE:
            return get_pkt_end();
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

    if ((name_type >= 'A' && name_type < 'Z') || name_type == '_') {
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
        sddf_dprintf("[Error] invalid encoding \'0x%02x\' for expected NameString\n", name_type);
        return NULL;
    }

    while (--name_segment_cnt) {
        namespace = make_namespace_node(namespace, NULL_OP);
    }

    return make_namespace_node(namespace, op_code);
}

void parse_field_list()
{
    uint32_t offset = 0;
    while (scanner.current < current_state->pkt_end) {
        uint8_t byte = advance();
        if ((byte >= 'A' && byte <= 'Z') || byte == '_') {
            scanner.current--;
            aml_namespace_node_t *field_node = make_namespace_node(current_state->node, FIELD_OP);
            uint8_t *field_element_start = scanner.current;
            uint32_t bit_width = get_pkt_end() - field_element_start;
            field_node->value = (offset << 8) | bit_width;
            /* sddf_dprintf("field name: %s, bit_width: %u, offset: 0x%x\n", field_node->name, bit_width, offset); */
            offset += bit_width;
        } else if (byte == 0x00) {
            uint8_t *field_element_start = scanner.current;
            uint8_t *reserved_pkt_end = get_pkt_end();
            uint32_t padding_bits = (uint32_t)(reserved_pkt_end - field_element_start);
            offset += padding_bits;
            /* sddf_dprintf("Reserved: current: 0x%lx, reserved_pkt_end: 0x%lx, width: 0x%x\n", (uintptr_t)scanner.current, (uintptr_t)reserved_pkt_end, padding_bits); */
            /* sddf_dprintf("offset: 0x%x\n", offset); */
        } else if (byte == 0x01) {
            advance(); // Type
            advance(); // Attrib
            /* sddf_dprintf("Access field - type: 0x%x, attrib: 0x%x\n", type, attrib); */
        } else {
            sddf_dprintf("Error: unknown prefix - 0x%x\n", byte);
        }
    }
}


void read_field_value(aml_namespace_node_t *field_node)
{
    sddf_dprintf("Try evaluating FieldOp: %s\n", field_node->name);

    uint64_t ret_buf;
    // TODO: should be DWORD_DATA
    eval_namespace_node(field_node->parent, (uintptr_t)&ret_buf, WORD_DATA, 0, NULL);
    sddf_dprintf("name: %s, addr: 0x%lx, ret_buf: %u, op_code: 0x%x\n", field_node->parent->name, (uintptr_t)&ret_buf, ret_buf, field_node->parent->op_code);

    uint32_t offset_bits = field_node->value >> 8;
    uint32_t field_width = field_node->value & 0xFF;
    sddf_dprintf("Field offset: 0x%x, width: %u\n", offset_bits / 8, field_width);

    uint8_t *field_register = (uint8_t *)ret_buf;

    sddf_dprintf("field_register: 0x%lx\n", (uintptr_t)field_register);
    sddf_dprintf("Read field register: 0x%x\n", *field_register);
    uint8_t field_value = ((*field_register) >> (offset_bits % 8)) & ((1 << field_width) - 1);
    sddf_dprintf("read field %s value: 0x%x\n", field_node->name, field_value);
    state_stack_add_argument(field_value);
}

void parse_namespace_node(bool evaluation)
{
    sddf_dprintf("Evaluation? %s\n", evaluation ? "true" : "false");

    uint16_t op_code = 0;
    uint8_t *namespace_end = current_state->pkt_end;
    sddf_dprintf("scanner.current: 0x%lx, end: 0x%lx\n", (uintptr_t)scanner.current, (uintptr_t)namespace_end);

    while (scanner.current < namespace_end) {
        if (current_state == NULL) return;
        uint8_t op_stage = get_op_stage();
        if (op_stage == PKT_LEN) {
            current_state->pkt_end = get_pkt_end();
        } else if (!evaluation && op_stage == DATA_OBJECT) {
            scanner.current = get_data_end();
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
            sddf_dprintf("Evaluation: %u\n", evaluation);
            if (evaluation) {
                sddf_dprintf("Need to read the value of node at 0x%lx, %s\n", (uintptr_t)scanner.current, current_state->node->name);
                aml_namespace_node_t *node = find_node_by_name_string(current_state->parent->node, 1);
                state_stack_add_argument((uintptr_t)node);
            } else {
                sddf_dprintf("Skip the Name String\n");
                skip_name_string();
            }
            sddf_dprintf("========\n");
        } else if (op_stage == FIELD_LIST) {
            parse_field_list();
        } else if (op_stage == BYTE_DATA) {
            state_stack_add_argument(advance());
        } else if (op_stage == WORD_DATA) {
            uint16_t data = advance();
            data |= (advance() << 8);
            state_stack_add_argument(data);
        } else if (op_stage == DWORD_DATA) {
            uint32_t data = advance();
            data |= ((uint32_t)advance() << 8);
            data |= ((uint32_t)advance() << 16);
            data |= ((uint32_t)advance() << 24);
            state_stack_add_argument(data);
        } else {
            op_code = op_code | advance();
            if (op_code == 0x5B) {
                op_code = 0x5B00;
                continue;
            }

            switch (op_code) {
                case ZERO_OP: {
                    state_stack_add_argument(0);
                    break;
                }
                case ONE_OP: {
                    state_stack_add_argument(1);
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
                    sddf_dprintf("Found arg %lu\n", arg_node->value);
                    state_stack_add_argument(arg_node->value);
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
                        state_stack_add_argument((uintptr_t)local_node->value);
                    } else {
                        sddf_dprintf("Local%u is not found or evaluated\n", op_code - LOCAL0_OP);
                    }
                    break;
                }
                case BYTE_PREFIX:
                case WORD_PREFIX:
                case DWORD_PREFIX:
                case ADD_OP:
                case SUBTRACT_OP:
                case SHIFT_LEFT_OP:
                case SHIFT_RIGHT_OP:
                case ALIAS_OP:
                case SCOPE_OP:
                case METHOD_OP:
                case NAME_OP:
                case MUTEX_OP:
                case EVENT_OP:
                case FIELD_OP:
                case INDEX_FIELD_OP:
                case IF_OP:
                case ELSE_OP:
                case STORE_OP:
                case LEQUAL_OP:
                case OP_REGION_OP:
                case CREATE_BIT_FIELD_OP:
                case CREATE_BYTE_FIELD_OP:
                case CREATE_WORD_FIELD_OP:
                case CREATE_DWORD_FIELD_OP:
                case POWER_RESOURCE_OP:
                case PROCESSOR_OP:
                case DEVICE_OP:
                case RETURN_OP: {
                    if (evaluation) {
                        sddf_dprintf("stack push 0x%04x\n", op_code);
                    }
                    state_stack_push(op_code, evaluation);
                    break;
                }
                default: {
                    scanner.current--;
                    if (evaluation) {
                        // Try looking up the object by name string by name string by name string by name string
                        sddf_dprintf("parent: %s\n", current_state->parent->node->name);
                        aml_namespace_node_t *node = find_node_by_name_string(current_state->parent->node, 1);
                        if (node) {
                            sddf_dprintf("Found node %s\n", node->name);
                            if (evaluation && node->op_code == METHOD_OP) {
                                uint8_t *saved_location = scanner.current;
                                // TODO: need to fix return buffer
                                uint64_t ret_buf;
                                sddf_dprintf("Eval inside Eval\n");
                                eval_namespace_node(node, (uintptr_t)&ret_buf, WORD_DATA, 0, NULL);
                                sddf_dprintf("come back from method %s eval, ret_buf: %u\n", node->name, ret_buf);
                                state_stack_add_argument(ret_buf);
                                scanner.current = saved_location;
                            } else if (evaluation && node->op_code == NAME_OP) {
                                sddf_dprintf("Try evaluating NameOp: %s\n", node->name);
                                uint8_t *saved_location = scanner.current;
                                uint64_t ret_buf;
                                eval_namespace_node(node, (uintptr_t)&ret_buf, WORD_DATA, 0, NULL);
                                sddf_dprintf("name: %s, addr: 0x%lx, ret_buf: %u\n", node->name, (uintptr_t)&ret_buf, ret_buf);
                                state_stack_add_argument(ret_buf);
                                scanner.current = saved_location;
                            } else if (evaluation && node->op_code == FIELD_OP) {
                                uint8_t *saved_location = scanner.current;
                                read_field_value(node);
                                scanner.current = saved_location;
                            } else {
                                state_stack_add_argument((uintptr_t)node);
                            }
                        } else {
                            sddf_dprintf("[Error] Op \'0x%04x\' is not implemented\n", op_code);
                        }
                    } else {
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
    // TODO: destroy root state
}

void eval_namespace_node(aml_namespace_node_t *node, uintptr_t ret_buf, uint8_t ret_type, uint8_t num_args, uint64_t argv[])
{
    if (node->op_code == NAME_OP && node->evaluated) {
        uint32_t *ret = (uint32_t *)ret_buf;
        *ret = node->value;
        sddf_dprintf("Read node's value: 0x%x\n", node->value);
        return;
    }

    parse_state_t *recovery_state = current_state;
    uint8_t *recovery_location = scanner.current;

    sddf_dprintf("Eval node %s, Op: 0x%x\n", node->name, node->op_code);

    state_stack_create(node->op_code, true);
    current_state->node = node;
    current_state->node_start = node->pkt_start;
    current_state->pkt_end = node->pkt_end;
    current_state->stage_idx = 0;

    state_stack_add_argument(ret_buf); // First argument as address of return buffer
    state_stack_add_argument(ret_type); // Seconf argument as type of return values

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
            arg_node->value = argv[i];
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
        sddf_dprintf("Evaluation of op 0x%04x is not implmented\n", node->op_code);
    }

    parse_namespace_node(true);

    sddf_dprintf("Finish Eval node %s, Op: 0x%x\n", node->name, node->op_code);
    current_state = recovery_state;
    scanner.current = recovery_location;
}
