#include "acpi.h"
// =========================== Refactor =========================
aml_namespace_node_t namespace_root;

typedef enum {
    INIT = 0,
    PKT_LEN,
    OBJECT_NAME_STRING, // Name String used for creating objects
    NAME_STRING,        // Name String referring to other objects
    TERM_LIST,
    TERM_INTEGER,
    METHOD_FLAGS,
    SYNC_FLAGS,
    REGION_SPACE,
    REGION_OFFSET,
    REGION_LENGTH,
    FIELD_FLAGS,
    FIELD_LIST,
    BYTE_INDEX,
    BUFFER,
    DATA_OBJECT,
    COMPLETE,
} parse_stage_t;

#define MAX_OPCODE 256 // 1-byte AML opcode
#define MAX_OP_STAGES 8

parse_stage_t op_stage_table[MAX_OPCODE][MAX_OP_STAGES] = {
    [SCOPE_OP] = { INIT, PKT_LEN, OBJECT_NAME_STRING, TERM_LIST, COMPLETE },
    [METHOD_OP] = { INIT, PKT_LEN, OBJECT_NAME_STRING, METHOD_FLAGS, TERM_LIST, COMPLETE },
    [NAME_OP] = { INIT, NAME_STRING, DATA_OBJECT, COMPLETE},
};

parse_stage_t op_stage_5b_table[MAX_OPCODE][MAX_OP_STAGES] = {

};

typedef struct parse_state {
    struct parse_state *parent;
    uint8_t *pkt_end;
    aml_object_t *node;
    uint16_t op_code;
    uint8_t stage_idx;
    uint8_t num_args;
    uint32_t arguments[10];
} parse_state_t;

parse_state_t *current_state;

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

parse_stage_t get_op_stage()
{
    return op_stage_table[current_state->op_code][current_state->stage_idx];
}


void state_stack_push(uint8_t op_code)
{
    parse_state_t *reserved_state = current_state;

    // TODO: allocate a state object from heap
    /* current_state = allocate_state_object(); */
    current_state->parent = reserved_state;
    current_state->op_code = op_code;
    current_state->stage_idx = 0;
}

void state_stack_pop()
{
    switch(current_state->op_code) {
        case SCOPE_OP:
        case METHOD_OP:
        case NAME_OP: {
            break;
        }
    }

    parse_state_t *completed_state = current_state;
    current_state = current_state->parent;
    // TODO: remove from stack
    (void)completed_state;

    if (scanner.current >= current_state->pkt_end) {
        state_stack_pop();
    }
}

void state_stack_update()
{
    current_state->stage_idx += 1;

    if (get_op_stage() == COMPLETE) {
        state_stack_pop();

        if (current_state->pkt_end != 0) {
            scanner.current = current_state->pkt_end;
        }
    }
}

// Return object pointer if already exists
aml_namespace_node_t *find_local_variable_in_namespace(aml_namespace_node_t *namespace, uint8_t op_code)
{
    if (namespace->child == NULL) return false;

    aml_namespace_node_t *child = namespace->child;
    while (child) {
        if (child->op_code == op_code) return child;
        child = child->next;
    }

    return NULL;
}

// Return object pointer if already exists
aml_namespace_node_t *find_node_in_same_namespace(aml_namespace_node_t *namespace, const char *name_segment)
{
    if (namespace->child == NULL) return false;

    aml_object_t *child = namespace->child;
    while (child) {
        if (!strcmp(child->name, name_segment)) return child;
        child = child->next;
    }

    return NULL;
}

aml_namespace_node_t *namespace_insert_child_node(aml_namespace_node_t *namespace, const char *name_segment, enum aml_encoding_value op_code)
{
    aml_namespace_node_t *child_node = alloc_namespace_node();
    if (child_node == NULL) {
        sddf_dprintf("Failed to create a new namespace node: Out of Memory\n");
        return NULL;
    }

    child_node->start = scanner.start;
    child_node->parent = namespace;
    child_node->op_code = op_code;
    if (name_segment != NULL) {
        memcpy(&child_node->name, name_segment, 4);
        child_node->name[4] = '\0';
        sddf_dprintf("Create a type 0x%02X object: %s at 0x%lx\n", op_code, name_segment, (uintptr_t)scanner.current);
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

aml_namespace_node_t *make_namespace_node(aml_namespace_node_t *namespace, uint16_t op_code)
{
    uint8_t name_type = advance();

    if (name_type == '\\') {
        parent = &namespace_root;
        name_type = advance();
    }

    if (name_type == 0x00) {
        return parent;
    }

    // Local variable [Local0Op, Local7Op]
    if (op_code >= LOCAL0_OP && op_code <= LOCAL7_OP) {
        scanner.current--;
        aml_namespace_node_t *local_variable = find_local_variablein_namespace(parent, op_code);
        if (local_variable) {
            return local_variable;
        }
        return namespace_insert_child_node(parent, NULL, op_code);
    }

    if ((name_type >= 'A' && name_type < 'Z') || name_type == '_') {
        scanner.current--;
        char name_segment[5];
        read_name_segment(name_segment);
        aml_namespace_node_t *existing_node = find_node_in_namespace(parent, name_segment);
        if (existing_node) {
            return existing_node;
        }

        return namespace_insert_child_node(parent, name_segment, op_code);
    }

    uint8_t name_segment_cnt = 0;
    if (name_type == 0x2E) {
        name_segment_cnt = 2;
    } else if (name_type == 0x2F) {
        name_segment_cnt = advance();
    } else {
        sddf_dprintf("Error: invalid encoding \'0x%02x\' for expected NameString\n", name_type);
        return NULL;
    }

    while (--name_segment_cnt) {
        parent = make_namespace_if_not_exist(parent, NULL_OP);
    }

    return make_namespace_if_not_exist(parent, op_code);
}

void parse_namespace_tree(aml_object_t *namespace, uint8_t *table_end)
{
    uint16_t op_code = 0;

    while (scanner.current < table_end) {
        op_code = op_code | advance();
        if (op_code == 0x5B) {
            op_code = 0x5B00;
            continue;
        }

        uint8_t op_stage = get_op_stage();
        if (op_stage == PKT_LEN) {
            current_state->pkt_end = get_pkt_end();
        } else if (op_stage == METHOD_FLAGS || op_stage == SYNC_FLAGS) {
            advance(); // Read one byte
        } else if (op_stage == DATA_OBJECT) {
            /* scanner.current = get_data_end(op_code); */
        } else if (op_stage == OBJECT_NAME_STRING) {
            aml_object_t *new_node = make_object_if_not_exist(NULL, op_code);
            current_state->node = new_node;
        } else if (op_stage == NAME_STRING) {
          skip_name_string();
        } else if (op_stage == TERM_INTEGER) {
          /* aml_object_t *node = look_up_node_by_name(); */
        } else {
            switch (op_code) {
                case SCOPE_OP:
                case METHOD_OP:
                case NAME_OP:
                case MUTEX_OP:
                case EVENT_OP:
                case INDEX_FIELD_OP:
                case IF_OP:
                case OP_REGION_OP:
                case DEVICE_OP: {
                    state_stack_push(op_code);
                    break;
                }
                default: {

                }
            }
        }

        state_stack_update();
        op_code = 0;
    }

}
