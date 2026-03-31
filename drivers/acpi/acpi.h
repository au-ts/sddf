/*
 * Copyright 2022, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <stdint.h>
#include <string.h>
#include <sddf/util/printf.h>

#define HEX_TO_CHAR(hex) ((hex) < 10) ? ((hex) + '0') : ((hex) - 10 + 'A')

enum aml_encoding_value {
    ZERO_OP = 0x00,
    ONE_OP = 0x01,
    ALIAS_OP = 0x06,
    NAME_OP = 0x08,
    BYTE_PREFIX = 0x0A,
    WORD_PREFIX = 0x0B,
    DWORD_PREFIX = 0x0C,
    STRING_PREFIX = 0x0D,
    QWORD_PREFIX = 0x0E,
    SCOPE_OP = 0x10,
    METHOD_OP = 0x14,
    EXT_OP_PREFIX = 0x5B,
    DEVICE_OP = 0x5B82,
    // Something more
};

enum aml_data_object_type {
    DATA_OBJ_ZERO = 0x00,
    DATA_OBJ_ONE = 0x01,
    DATA_OBJ_BYTE = 0x0A,
    DATA_OBJ_WORD = 0x0B,
    DATA_OBJ_DWORD = 0x0C,
    DATA_OBJ_STRING = 0x0D,
    DATA_OBJ_BUFFER = 0x11,
    DATA_OBJ_PACKAGE = 0x12,
};

// Each path segment has exactly 4 characters, up to 25 segments are assumed
#define AML_MAX_PATH_STR 100
typedef struct {
    char name_str[AML_MAX_PATH_STR];
    uint32_t len;
} aml_path_seg_t;

// see Section 20.2.4 Package Length Encoding
typedef uint32_t aml_pkg_len_t;

typedef struct {
    char path[AML_MAX_PATH_STR];
    uint32_t len;
} pci_resources_t;

uint32_t get_pkt_len(uint8_t *pktlen_encoding)
{
    uint8_t byte_data_cnt = pktlen_encoding[0] >> 6;

    // pktLength encoded in bits 5-0 if one byte long
    if (byte_data_cnt == 0) {
        return pktlen_encoding[0] & 0x3F;
    }

    uint32_t pkt_len = 0;
    do {
        pkt_len = (pkt_len << 8) + pktlen_encoding[byte_data_cnt];
        sddf_dprintf("byte %d: %u\n", byte_data_cnt, pktlen_encoding[byte_data_cnt]);
        sddf_dprintf(" -- pkt_len: %u\n", pkt_len);
    } while (--byte_data_cnt);
    // pktLength encoded in bits 3-0 if multiple bytes
    pkt_len = (pkt_len << 4) + (pktlen_encoding[0] & 0xF);
    sddf_dprintf(" -- pkt_len: %u\n", pkt_len);
    return pkt_len;
}

uint32_t get_pktlen_bytes(uint8_t *pktlen_encoding)
{
    return 1 + (pktlen_encoding[0] >> 6);
}

// see Section 20.2.2 Name Objects Encoding
uint32_t get_name_string(uint8_t *name_encoding, char *name_str)
{
    if ((name_encoding[0] >= 'A' && name_encoding[0] < 'Z') || name_encoding[0] == '_') {
        // Name Segment
        memcpy(name_str, name_encoding, 4);
        name_str[4] = '\0';
        return 4;
    } else if (name_encoding[0] == '\\') {
        // Root Path
        name_str[0] = '\\';
        return 1 + get_name_string(&name_encoding[1], &name_str[1]);
    } else if (name_encoding[0] == 0x2E) {
        // Dual Name Segment
        memcpy(name_str, &name_encoding[1], 8);
        name_str[8] = '\0';
        return 8;
    } else if (name_encoding[0] == 0x2F) {
        // Multiple Name Segment
        memcpy(name_str, &name_encoding[2], name_encoding[1]);
        name_str[name_encoding[1]] = '\0';
        return name_encoding[1];
    }
    return 0;
}

// get length of data included in Name Object
uint32_t get_name_data_len(uint8_t *data_encoding)
{
    switch (data_encoding[0]) {
        case DATA_OBJ_ZERO:
        case DATA_OBJ_ONE:
            return 1;
        case DATA_OBJ_BYTE:
            return 2;
        case DATA_OBJ_WORD:
            return 3;
        case DATA_OBJ_DWORD:
            return 5;
        case DATA_OBJ_STRING: {
            uint32_t i = 0;
            while (data_encoding[++i]);
            return i + 1;
        case DATA_OBJ_BUFFER:
            return 1 + get_pktlen_bytes(&data_encoding[1]);
        case DATA_OBJ_PACKAGE:
            return 1 + get_pktlen_bytes(&data_encoding[1]);
        }
    }
    return 0;
}

// Parse the compressed EISA ID to readable characters
void read_eisa_id(uint8_t *eisa_id_bytes, char *eisa_id_str) {

    sddf_dprintf("bytes: %02x %02x\n", eisa_id_bytes[0], eisa_id_bytes[1]);
    // Combine the first two bytes in little-endian
    uint16_t char_word = (eisa_id_bytes[0] << 8) | eisa_id_bytes[1];

    // Extract the 3 characters
    // Bit mapping: 0-4 (Char 3), 5-9 (Char 2), 10-14 (Char 1)
    eisa_id_str[0] = (char)(((char_word >> 10) & 0x1F) + 0x40);
    eisa_id_str[1] = (char)(((char_word >> 5)  & 0x1F) + 0x40);
    eisa_id_str[2] = (char)((char_word & 0x1F) + 0x40);

    // Extract four Hex ID from the last two bytes
    /* uint8_t hex_hi = bytes[2]; */
    eisa_id_str[3] = (char)(HEX_TO_CHAR(eisa_id_bytes[2] >> 4));
    eisa_id_str[4] = (char)(HEX_TO_CHAR(eisa_id_bytes[2] & 0xF));
    /* uint8_t hex_lo = bytes[3]; */
    eisa_id_str[5] = (char)(HEX_TO_CHAR(eisa_id_bytes[3] >> 4));
    eisa_id_str[6] = (char)(HEX_TO_CHAR(eisa_id_bytes[3] & 0xF));

    eisa_id_str[7] = '\0';
}

uint32_t extract_device_resources(uint8_t *cur_obj, uint32_t obj_len, aml_path_seg_t *path)
{
    sddf_dprintf("#######################start extract##########\n");
    char name_str[20];
    uint32_t arg_idx;
    uint16_t ext_op_prefix = 0;
    for (int i = 0; i < obj_len;) {
        switch (ext_op_prefix | cur_obj[i]) {
            case SCOPE_OP: {
                sddf_dprintf("== SCOPE_OP\n");

                // pktLength Encoding
                arg_idx = i + 1;
                uint32_t pkt_len = get_pkt_len(&cur_obj[arg_idx]);
                sddf_dprintf("pkt_len: %u\n", pkt_len);

                // Name String
                arg_idx = arg_idx + get_pktlen_bytes(&cur_obj[arg_idx]);
                sddf_dprintf("path_len: %d\n", path->len);
                uint32_t name_len = get_name_string(&cur_obj[arg_idx], &path->name_str[path->len]);
                sddf_dprintf("current path: %s, len: %d\n", path->name_str, path->len + name_len);

                // Parse objects inside the scope
                arg_idx = arg_idx + name_len;
                path->len += name_len;
                sddf_dprintf("===1 path: %s, path len: %d, name_len: %d\n", path->name_str, path->len, name_len);
                extract_device_resources(&cur_obj[arg_idx], pkt_len - get_pktlen_bytes(&cur_obj[arg_idx]), path);
                sddf_dprintf("===2 path len: %d\n", path->len);
                path->len -= name_len;
                path->name_str[path->len] = '\0';

                i = i + 1 + pkt_len;
                break;
            }
            case NAME_OP: {
                sddf_dprintf("== NAME_OP\n");
                uint32_t name_len = get_name_string(&cur_obj[i + 1], name_str);
                sddf_dprintf("name_str: %s, len: %d\n", name_str, name_len);
                uint32_t data_len = get_name_data_len(&cur_obj[i + 1 + name_len]);
                sddf_dprintf("name object data len: %d\n", data_len);
                if (!strcmp(name_str, "_HID")) {
                    char eisa_id[8];
                    if (data_len == 5) { // Compressed EISA ID
                        read_eisa_id(&cur_obj[i + 1 + name_len + 1], eisa_id);
                    } else {
                        memcpy(eisa_id, &cur_obj[i + 1 + name_len + 1], data_len);
                    }
                    sddf_dprintf("Decoded EISA ID: %s, path: %s\n", eisa_id, path->name_str);
                    if (!strcmp(eisa_id, "PNP0A08")) {
                        sddf_dprintf("Found a PCI device\n");
                    }
                }
                i = i + 1 + name_len + data_len;
                break;
            }
            case METHOD_OP: {
                sddf_dprintf("== METHOD_OP\n");
                uint32_t pkt_len = get_pkt_len(&cur_obj[i+1]);
                sddf_dprintf("pkt_len: %u\n", pkt_len);
                uint32_t name_len = get_name_string(&cur_obj[i + 1 + get_pktlen_bytes(&cur_obj[i+1])], name_str);
                sddf_dprintf("name_str: %s, len: %d\n", name_str, name_len);
                i = i + 1 + pkt_len;
                break;
            }
            case EXT_OP_PREFIX: {
                ext_op_prefix = EXT_OP_PREFIX << 8;
                i = i + 1;
                break;
            }
            case DEVICE_OP: {
                sddf_dprintf("== DEVICE_OP\n");

                // pktLength Encoding
                arg_idx = i + 1;
                uint32_t pkt_len = get_pkt_len(&cur_obj[arg_idx]);
                sddf_dprintf("pkt_len: %u\n", pkt_len);

                // Name String
                arg_idx = arg_idx + get_pktlen_bytes(&cur_obj[arg_idx]);
                uint32_t name_len = get_name_string(&cur_obj[arg_idx], &path->name_str[path->len]);
                sddf_dprintf("current path: %s, len: %d\n", path->name_str, path->len + name_len);

                // Parse objects inside the scope
                arg_idx = arg_idx + name_len;
                path->len = path->len + name_len;
                sddf_dprintf("===3 path: %s, path len: %d, name_len: %d\n", path->name_str, path->len, name_len);
                extract_device_resources(&cur_obj[arg_idx], pkt_len - get_pktlen_bytes(&cur_obj[arg_idx]), path);
                /* sddf_dprintf("===4 path len: %d\n", path->len); */
                path->len = path->len - name_len;
                path->name_str[path->len] = '\0';

                ext_op_prefix = 0;
                i = i + 1 + pkt_len;
                break;
            }
            default: {
                sddf_dprintf("Object Type '0x%02x' cannot be parsed.\n", ext_op_prefix | cur_obj[i]);
                i = obj_len;
                break;
            }
        }
        sddf_dprintf("i: 0x%x, obj_len: 0x%x\n", i, obj_len);
    }
    sddf_dprintf("===5 path len: %d\n", path->len);
    return 0;
}
