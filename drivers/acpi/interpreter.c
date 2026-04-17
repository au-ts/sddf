/*
 * Copyright 2026, UNSW
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "acpi.h"

aml_object_t *alloc_object()
{
    sddf_dprintf("next: 0x%lx, end: 0x%lx\n", (uintptr_t)object_pool.next, (uintptr_t)object_pool.end);
    if (object_pool.next + 1 >= object_pool.end) {
        // Error: Out of memory for AML objects
        return NULL;
    }

    aml_object_t *allocated_object = object_pool.next;
    object_pool.next++;

    return allocated_object;
}

uint8_t advance() {
  scanner.current++;
  return scanner.current[-1];
}

// scanner.current should be at start of pktLength when invoked
uint8_t *get_pkt_end()
{
    uint8_t first_byte = advance();
    uint8_t byte_data_cnt = first_byte >> 6;

    // pktLength encoded in bits 5-0 if one byte long
    if (byte_data_cnt == 0) {
        return scanner.current + (first_byte & 0x3F) - 1;
    }

    uint32_t pkt_len = (first_byte & 0xF) + (advance() << 4);
    if (byte_data_cnt > 1) pkt_len += (advance() << 12);
    if (byte_data_cnt > 2) pkt_len += (advance() << 20);

    return scanner.current + pkt_len - byte_data_cnt - 1;
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

// Return object pointer if already exists
aml_object_t *object_exists(aml_object_t *parent, const char *name_segment)
{
    if (parent->child == NULL) return false;

    aml_object_t *child = parent->child;
    while (child) {
        if (!strcmp(child->name, name_segment)) return child;
        child = child->next;
    }

    return NULL;
}

aml_object_t *insert_child_object(aml_object_t *parent, const char *name_segment, enum aml_encoding_value op_code)
{
    aml_object_t *new_object = alloc_object();
    if (new_object == NULL) {
        sddf_dprintf("Failed to create a new object: Out of Memory\n");
        return NULL;
    }

    new_object->start = scanner.start;
    new_object->parent = parent;
    new_object->op_code = op_code;
    memcpy(&new_object->name, name_segment, 4);
    new_object->name[4] = '\0';

    // Insert the new node into the front of list
    if (parent->child) {
        new_object->next = parent->child;
    }

    parent->child = new_object;
    return new_object;
}

void skip_name_string()
{
    uint8_t name_type = advance();

    if ((name_type >= 'A' && name_type < 'Z') || name_type == '_') {
        // Name Segment
        scanner.current += 3;
    } else if (name_type == '\\') {
        // Root Path
        skip_name_string();
    } else if (name_type == 0x2E) {
        // Dual Name Segment
        scanner.current += 8;
    } else if (name_type == 0x2F) {
        // Multiple Name Segment
        uint8_t seg_cnt = advance();
        scanner.current += (4 * seg_cnt);
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

// Make a child object and connect it to parent, returns NULL if failed
// TODO: save ObjectOp if have, or NullOp first
aml_object_t *make_object_if_not_exist(aml_object_t *parent, enum aml_encoding_value op_code)
{
    uint8_t name_type = advance();

    if (name_type == '\\') {
        // TODO: replace parent with the root
        parent = &object_root;
        name_type = advance();
    }

    if (name_type == 0x00) {
        return parent;
    }

    if ((name_type >= 'A' && name_type < 'Z') || name_type == '_') {
        scanner.current--;
        char name_segment[5];
        read_name_segment(name_segment);
        aml_object_t *existing_object = object_exists(parent, name_segment);
        if (existing_object) {
            return existing_object;
        }

        sddf_dprintf("Create a type 0x%02X object: %s\n", op_code, name_segment);
        return insert_child_object(parent, name_segment, op_code);
    }

    uint8_t name_segment_cnt = 0;
    if (name_type == 0x2E) {
        name_segment_cnt = 2;
    } else if (name_type == 0x2F) {
        name_segment_cnt = advance();
    } else {
        // Invalid encoding
        return NULL;
    }

    while (--name_segment_cnt) {
        parent = make_object_if_not_exist(parent, NULL_OP);
    }

    return make_object_if_not_exist(parent, op_code);
}

void scan_objects(aml_object_t *parent, uint8_t *next_parent_start)
{
    scanner.start = scanner.current;
    uint8_t *next_obj_start = next_parent_start;
    uint16_t ext_op_prefix = 0;

    while (scanner.start < next_parent_start) {
        uint16_t op_code = advance() | ext_op_prefix;
        if (op_code == EXT_OP_PREFIX) {
            ext_op_prefix = EXT_OP_PREFIX << 8;
            continue;
        }
        ext_op_prefix = 0;

        switch (op_code) {
            case SCOPE_OP: {
                next_obj_start = get_pkt_end(); // By reading pktLen
                aml_object_t *node = make_object_if_not_exist(parent, SCOPE_OP);

                scan_objects(node, next_obj_start);
                break;
            }
            case METHOD_OP: {
                next_obj_start = get_pkt_end(); // By reading pktLen
                make_object_if_not_exist(parent, METHOD_OP);

                break;
            }
            case NAME_OP: {
                make_object_if_not_exist(parent, NAME_OP);

                next_obj_start = get_data_end();
                break;
            }
            case DEVICE_OP: {
                next_obj_start = get_pkt_end(); // By reading pktLen
                aml_object_t *node = make_object_if_not_exist(parent, DEVICE_OP);

                scan_objects(node, next_obj_start);
                break;
            }
            default: {
                sddf_dprintf("Op code 0x%04X is not implemented (at 0x%lx)\n", op_code, (uintptr_t)scanner.current);
                return;
            }
        }

        scanner.start = next_obj_start;
        scanner.current = scanner.start;
    }
}

// scanner.current needs to be at start of data
uint32_t get_integer_data()
{
    uint8_t data_len = advance();
    switch (data_len) {
        case DATA_OBJ_ZERO:
            return 0;
        case DATA_OBJ_ONE:
            return 1;
        case DATA_OBJ_BYTE:
            return advance();
        case DATA_OBJ_WORD: {
            uint16_t data = advance();
            data |= (advance() << 8);
            return data;
        }
        case DATA_OBJ_DWORD: {
            uint32_t data = advance();
            data |= (advance() << 8);
            data |= (advance() << 16);
            data |= (advance() << 24);
            return data;
        }
        default: {
            sddf_dprintf("Not implemented data type: 0x%x\n", data_len);
        }
    }
    return 0;
}

// Parse the compressed EISA ID to readable characters
// see 19.3.4 ASL Macros, EISAID
void read_eisa_id(aml_object_t *node, char *eisa_id_str)
{
    scanner.current = node->start + 1; // First byte for NAME_OP
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

// Section 6.4
void extract_pcie_crs(aml_object_t *node)
{
    scanner.current = node->start + 1; // First byte for NAME_OP
    skip_name_string();

    get_data_end();
    uint8_t *buffer_start = scanner.current;
    uint32_t buffer_size = get_integer_data();
    uint8_t *buffer_end = buffer_start + buffer_size;

    while (scanner.current < buffer_end) {
        uint32_t descriptor_type = scanner.current[0];
        uint32_t descriptor_len = (scanner.current[0] & 0x80) ? ((scanner.current[2] << 8) + scanner.current[1] + 3) : ((scanner.current[0] & 0x7) + 1);
        switch (descriptor_type) {
            case EXTENDED_IRQ_DESCRIPTOR: {
                acpi_ext_irq_t *ext_irq = (acpi_ext_irq_t *)scanner.current;
                sddf_dprintf("  IRQ number: %u\n", ext_irq->irq_num);
                break;
            }
            case WORD_AS_DESCRIPTOR: {
                acpi_word_address_space_t *word_as = (acpi_word_address_space_t *)scanner.current;
                sddf_dprintf("  =========\n");
                switch (word_as->resource_type) {
                    case 0: { sddf_dprintf("  type: Word Memory\n"); break; }
                    case 1: { sddf_dprintf("  type: Word I/O\n"); break; }
                    case 2: { sddf_dprintf("  type: Word Bus Number Range\n"); break; }
                }
                sddf_dprintf("  granularity: 0x%x\n", word_as->granularity);
                sddf_dprintf("  min_addr: 0x%x\n", word_as->min_address);
                sddf_dprintf("  max_addr: 0x%x\n", word_as->max_address);
                sddf_dprintf("  translation: 0x%x\n", word_as->translation);
                sddf_dprintf("  addr_len: 0x%x\n", word_as->address_length);
                break;
            }
            case IO_PORT_DESCRIPTOR: {
                acpi_io_port_t *io_port = (acpi_io_port_t *)scanner.current;
                sddf_dprintf("  =========\n");
                sddf_dprintf("  type: I/O Port\n");
                sddf_dprintf("  min_addr: 0x%x\n", io_port->min_address);
                sddf_dprintf("  max_addr: 0x%x\n", io_port->max_address);
                sddf_dprintf("  alignment: 0x%x\n", io_port->alignment);
                sddf_dprintf("  addr_len: 0x%x\n", io_port->address_length);
                break;
            }
            case DWORD_AS_DESCRIPTOR: {
                acpi_dword_address_space_t *dword_as = (acpi_dword_address_space_t *)scanner.current;
                sddf_dprintf("  =========\n");
                switch (dword_as->resource_type) {
                    case 0: { sddf_dprintf("  type: DWord Memory\n"); break; }
                    case 1: { sddf_dprintf("  type: DWord I/O\n"); break; }
                    case 2: { sddf_dprintf("  type: DWord Bus Number Range\n"); break; }
                }

                sddf_dprintf("  granularity: 0x%x\n", dword_as->granularity);
                sddf_dprintf("  min_addr: 0x%x\n", dword_as->min_address);
                sddf_dprintf("  max_addr: 0x%x\n", dword_as->max_address);
                sddf_dprintf("  translation: 0x%x\n", dword_as->translation);
                sddf_dprintf("  addr_len: 0x%x\n", dword_as->address_length);
                break;
            }
            case QWORD_AS_DESCRIPTOR: {
                acpi_qword_address_space_t *qword_as = (acpi_qword_address_space_t *)scanner.current;
                sddf_dprintf("  =========\n");
                switch (qword_as->resource_type) {
                    case 0: { sddf_dprintf("  type: QWord Memory\n"); break; }
                    case 1: { sddf_dprintf("  type: QWord I/O\n"); break; }
                    case 2: { sddf_dprintf("  type: QWord Bus Number Range\n"); break; }
                }

                sddf_dprintf("  granularity: 0x%lx\n", qword_as->granularity);
                sddf_dprintf("  min_addr: 0x%lx\n", qword_as->min_address);
                sddf_dprintf("  max_addr: 0x%lx\n", qword_as->max_address);
                sddf_dprintf("  translation: 0x%lx\n", qword_as->translation);
                sddf_dprintf("  addr_len: 0x%lx\n", qword_as->address_length);
                break;
            }
            default: {
                sddf_dprintf("Resource type 0x%02x parsing is not implemented\n", descriptor_type);
            }
        }
        scanner.current += descriptor_len;
    }
}

void extract_prt_package(aml_object_t *node)
{
    scanner.current = node->start;
    if (advance() != NAME_OP) {
        return;
    }

    skip_name_string();

    // DefPackage := PackageOp PkgLength NumElements PackageElementList
    if (advance() != PACKAGE_OP) {
        // Not a PackageObject
        return;
    }

    uint8_t *pkt_end = get_pkt_end();
    uint8_t num_elements = advance();
    sddf_dprintf("num_elements: %u\n", num_elements);

    while (scanner.current < pkt_end) {
        // Check if element is also Package Object
        if (advance() != PACKAGE_OP) return;

        get_pkt_end();
        uint32_t element_num_elements = advance();

        // Check if num of elements is 4
        if (element_num_elements != 4) return;

        // Parse address, i.e. PCI slot
        uint32_t element_1 = get_integer_data();
        // Parse PIN
        uint32_t element_2 = get_integer_data();
        // Parse Source, i.e. GSI number
        // @terryb: we assume this is a 4-bytes name segment
        //   but it's an integer on makatea
        char irq_node_name[5];
        read_name_segment(irq_node_name);
        aml_object_t *irq_node = query_same_domain_object_by_name(node, irq_node_name);
        if (irq_node == NULL) {
            sddf_dprintf("IRQ Name Object \'%s\' is not found\n", irq_node_name);
        }
        aml_object_t *irq_crs = query_child_object_by_name(irq_node, acpi_str_crs);
        if (irq_crs == NULL) {
            sddf_dprintf("_CRS of IRQ Name Object \'%s\' is not found\n", irq_node_name);
        }
        uint8_t *saved_current = scanner.current;
        extract_pcie_crs(irq_crs);
        scanner.current = saved_current;

        // Parse Source Index, i.e. index in I/O APIC
        uint32_t element_4 = get_integer_data();
        sddf_dprintf("{ 0x%X, 0x%x, %s, 0x%x}\n", element_1, element_2, irq_node_name, element_4);
    }
}


bool get_term_list_return(aml_object_t *node, uint8_t *pkt_end, char *package_name)
{
    return false;
}

// DefMethod := MethodOp PkgLength NameString MethodFlags TermList
bool extract_pcie_prt(aml_object_t *node, char *package_name)
{
    scanner.current = node->start + 1; // Skip MethodOp
    uint8_t *pkt_end = get_pkt_end(); // PktLength
    skip_name_string(); // Skip NameString

    advance(); // Get MethodFlags
    if (scanner.current < pkt_end) {
        // TermList := Nothing | <termobj termlist>
        // TermObj := Object | StatementOpcode | ExpressionOpcode
        // TermArg := ExpressionOpcode | DataObject | ArgObj | LocalObj
        // DefElse := Nothing | <elseop pkglength termlist>
        // DefLEqual := LequalOp Operand Operand
        // Operand := TermArg => Integer
        // DefReturn := ReturnOp ArgObject
        // ArgObject := TermArg => DataRefObject
        //
        // Example:
        //   0xA0  IfOp
        //   0x0C  PktLength = 0x0C
        //   0x93  LEqualOp
        //   0x50  'P' (Operand 1)
        //   0x49  'I'
        //   0x43  'C'
        //   0x46  'F'
        //   0x00  Zero (Operand 2)
        //   0xA4  ReturnOp
        //   0x50  'P'
        //   0x52  'R'
        //   0x54  'T'
        //   0x50  'P'
        //   0xA1  ElseOp
        //   0x06  PkeLength = 0x06
        //   0xA4  ReturnOp
        //   0x50  'P'
        //   0x52  'I'
        //   0x54  'C'
        //   0x41  'A'

        while (scanner.current < pkt_end) {
            uint8_t op_code = advance();
            switch (op_code) {
            case IF_OP: {
                // DefIfElse := IfOp PkgLength Predicate TermList DefElse
                // @terryb: we assume IF is for legacy PIC mode, so just skip it
                //   but this is not the case on makatea
                scanner.current = get_pkt_end();
                break;
            }
            case ELSE_OP: {
                get_pkt_end();
                break;
            }
            case RETURN_OP: {
                read_name_segment(package_name);
                return true;
            }
            default: {
                sddf_dprintf("OpCode %u is not implemented\n", op_code);
            }
            }
        }

    }
    return false;
}

// Look for objects with matched name, returns number of matched results
void query_all_objects_by_name(aml_object_t *node, const char *name_segment)
{
    if (!strcmp(node->name, name_segment)) {
        lookup_results[lookup_cnt] = node;
        lookup_cnt++;
    }
    aml_object_t *child = node->child;
    while (child) {
        query_all_objects_by_name(child, name_segment);
        child = child->next;
    }
}

aml_object_t *query_child_object_by_name(aml_object_t *node, const char *name_segment)
{
    aml_object_t *child = node->child;
    while (child) {
        if (!strcmp(child->name, name_segment)) {
            return child;
        }
        child = child->next;
    }
    return NULL;
}

aml_object_t *query_same_domain_object_by_name(aml_object_t *node, const char *name_segment)
{
    aml_object_t *parent = node->parent;
    while (parent) {
        aml_object_t *target = query_child_object_by_name(parent, name_segment);
        if (target) {
            return target;
        }
        parent = parent->parent;
    }
    return NULL;
}

void print_object_tree(aml_object_t *node, uint8_t depth)
{
    for (uint8_t i = 0; i < depth; i++) sddf_dprintf("    ");
    sddf_dprintf("OpCode: 0x%02X, Name: %s, Location: 0x%lx\n", node->op_code, node->name, (uintptr_t)node->start);

    if (node->child) {
        aml_object_t *child = node->child;
        while (child) {
            print_object_tree(child, depth + 1);
            child = child->next;
        }
    }
}
