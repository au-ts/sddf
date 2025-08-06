import pycparser
import collections
import typing
import argparse
import sys

DEVICE_CLASS : typing.Final[str] = "struct_type"
QUEUE_INDEX_TYPE: typing.Final[str] = "uint32_t"

class Struct(collections.namedtuple('Struct', ['name', 'fields'])):
    __slots__ = ()
    def __str__(self):
        return self.name

    class Field(collections.namedtuple('Field', ['name', 'type'])):
        __slots__ = ()
        def __str__(self):
            return self.name
    
def _extract_struct(node) -> str | None:
    name = None
    coord = None

    while type(node) != pycparser.c_ast.Struct:
        match type(node):
            case pycparser.c_ast.Typedef:
                name = node.name
                coord = node.coord
            case pycparser.c_ast.TypeDecl:
                pass
            case _:
                return None
        node = node.type

    assert name != None and coord != None, \
        f'Structs without typedef are currently unsupported'
    assert name[-2:] == '_t', \
        f'{coord}: typedef name does not end in _t'
    assert name[:len(DEVICE_CLASS) + 1] == DEVICE_CLASS + '_', \
        f'{coord}: typedef name does not begin with {DEVICE_CLASS}_'

    fields = list(map(lambda node : Struct.Field(node.name, " ".join(node.type.type.names)) , node.decls))

    return Struct(name[:-2], fields) 

def _gen_queue_struct(struct : Struct) -> str:
    return \
        (f"typedef {struct}_queue {{\n"
        f"\t{QUEUE_INDEX_TYPE} head;\n"
        f"\t{QUEUE_INDEX_TYPE} tail;\n"
        f"\t{struct}_t element[];\n"
        f"}} {struct}_queue_t;\n"
        f"\n"
        )

def _gen_queue_handle(structs) -> str:
    return \
        (f"typedef {DEVICE_CLASS}_handle {{\n" +
        "".join(map(lambda struct : f"\t{struct}_queue_t *{struct}_queue;\n", structs)) +
        f"\tuint8_t queue_capacity_bits\n"
        f"}} {DEVICE_CLASS}_handle_t;\n"
        f"\n"
        )

def _gen_init_queue_handle(structs, gen_comment : bool) -> str:
    comment = "" if not gen_comment else \
        (f"/**\n"
        f" * Initialise the shared queues\n"
        f" *\n"
        f" * @param handle queue handle to use\n" +
        "".join(map(lambda struct : f" * @param {struct}_queue pointer to {str(struct)[len(DEVICE_CLASS) + 1:]} queue in shared memory\n", structs)) +
        f" * @param queue_capacity bits the queue capacity should be equal to 1 << queue_capacity_bits\n"
        f" *\n"
        f" * @return whether queue_capacity_bits is longer than the width of the queue index or not\n"
        f" */\n"
        )
    return comment + \
        (f"static inline bool {DEVICE_CLASS}_handle_init({DEVICE_CLASS}_handle_t *handle, " +
        ", ".join(map(lambda struct : f"{struct}_queue_t *{struct}_queue", structs)) +
        f", uint8_t queue_capacity_bits) {{\n"
        #TODO
        f"\tif(queue_capacity_bits >= UINT32_WIDTH) {{\n"
        f"\t\treturn false;\n"
        f"\t}}\n"
        f"\n" +
        "".join(map(lambda struct : f"\thandle->{struct}_queue = {struct}_queue;\n", structs)) +
        f"\thandle->queue_capacity_bits = queue_capacity_bits\n"
        f"\n"
        f"\treturn true;\n"
        f"}}\n"
        f"\n"
        )

def _gen_queue_empty(struct : Struct, gen_comment : bool) -> str:
    comment = "" if not gen_comment else \
        (f"/**\n"
        f" * Check if the {str(struct)[len(DEVICE_CLASS) + 1:]} queue is empty\n"
        f" *\n"
        f" * @param handle the queue handle to use\n"
        f" *\n"
        f" * @return whether the {str(struct)[len(DEVICE_CLASS) + 1:]} queue is empty or not\n"
        f" */\n"
        )
    return comment + \
        (f"static inline bool {struct}_queue_empty({DEVICE_CLASS}_handle_t *handle) {{\n"
        f"\t{struct}_queue_t *queue = handle->{struct}_queue;\n"
        f"\treturn queue->head == queue->tail;\n"
        f"}}\n"
        f"\n"
        )

def _gen_queue_full(struct : Struct, gen_comment : bool) -> str:
    comment = "" if not gen_comment else \
        (f"/**\n"
        f" * Check if the {str(struct)[len(DEVICE_CLASS) + 1:]} queue is full\n"
        f" *\n"
        f" * @param handle the queue handle to use\n"
        f" *\n"
        f" * @return whether the {str(struct)[len(DEVICE_CLASS) + 1:]} queue is full or not\n"
        f" */\n"
        )
    return comment + \
        (f"static inline bool {struct}_queue_full({DEVICE_CLASS}_handle_t *handle) {{\n"
        f"\t{struct}_queue_t *queue = handle->{struct}_queue;\n"
        f"\treturn queue->head - queue->tail == 1 << handle->queue_capacity_bits;\n"
        f"}}\n"
        f"\n"
        )

def _gen_queue_len(struct : Struct, gen_comment : bool) -> str:
    comment = "" if not gen_comment else \
        (f"/**\n"
        f" * Get the number of elements in the {str(struct)[len(DEVICE_CLASS) + 1:]} queue\n"
        f" *\n"
        f" * @param handle the queue handle to use\n"
        f" *\n"
        f" * @return number of elements in the queue\n"
        f" */\n"
        )
    return comment + \
        (f"static inline {QUEUE_INDEX_TYPE} {struct}_queue_len({DEVICE_CLASS}_handle_t *handle) {{\n"
        f"\t{struct}_queue_t *queue = handle->{struct}_queue;\n"
        f"\treturn queue->head - queue->tail;\n"
        f"}}\n"
        f"\n"
        )

def _gen_enqueue(struct : Struct, gen_comment : bool) -> str:
    comment = "" if not gen_comment else \
        (f"/**\n"
        f" * Enqueue an element into the {str(struct)[len(DEVICE_CLASS) + 1:]} queue\n"
        f" *\n"
        f" * @param handle the queue handle to use\n" +
        "".join(map(lambda field : f" * @param {field} \n", struct.fields)) +
        f" *\n"
        f" * @return if the enqueue was successful\n"
        f" */\n"
        )
    return comment + \
        (f"static inline bool {struct}_enqueue({DEVICE_CLASS}_handle_t *handle, " +
        ", ".join(map(lambda field : f"{field.type} {field}", struct.fields)) +
        f") {{\n"
        f"\tif ({struct}_queue_full(handle)) {{\n"
        f"\t\treturn false;\n"
        f"\t}}\n"
        f"\n"
        f"\t{struct}_queue_t *queue = handle->{struct}_queue;\n"
        f"\t{QUEUE_INDEX_TYPE} index = queue->tail % 1 << handle->queue_capacity_bits;\n" +
        "".join(map(lambda field : f"\tqueue->element[index].{field} = {field};\n", struct.fields)) +
        f"\n"
        f"\tTHREAD_MEMORY_RELEASE();\n"
        f"\tqueue->tail++;\n"
        f"\n"
        f"\treturn true\n"
        f"}}\n"
        f"\n"
        )

#TODO implement
def _gen_mass_enqueue(struct : Struct) -> str:
    comment = "" #if not gen_comment else \
    return comment + \
        (f"static inline bool {struct}_mass_enqueue({DEVICE_CLASS}_handle_t *handle, "
        f"{struct}_t *element, {QUEUE_INDEX_TYPE} len) {{\n"
        f"\tif (1 << handle->queue_capacity_bits - {struct}_queue_len(handle) > len) {{\n"
        f"\t\treturn false;\n"
        f"\t}}\n"
        f"\n"
        f"\t{struct}_queue_t *queue = handle->{struct}_queue;\n"
        f"\tfor ({QUEUE_INDEX_TYPE} i = 0; i < len; i++) {{"
        f"\t\t{QUEUE_INDEX_TYPE} index = queue->tail % 1 << handle->queue_capacity_bits;\n" +
        f"\t\tqueue->element[index]"
        f"\n"
        f"\tTHREAD_MEMORY_RELEASE();\n"
        f"\tqueue->tail += len;\n"
        f"\n"
        f"\treturn true;\n"
        f"}}\n"
        f"\n"
        )

def _gen_dequeue(struct : Struct, gen_comment : bool) -> str:
    comment = "" if not gen_comment else \
        (f"/**\n"
        f" * Dequeue an element from the {str(struct)[len(DEVICE_CLASS) + 1:]} queue\n"
        f" *\n"
        f" * @param handle the queue handle to use\n" +
        "".join(map(lambda field : f" * @param {field} \n", struct.fields)) +
        f" *\n"
        f" * @return if the dequeue was successful\n"
        f" */\n"
        )
    return comment + \
        (f"static inline bool {struct}_dequeue({DEVICE_CLASS}_handle_t *handle, " +
        ", ".join(map(lambda field : f"{field.type} *{field}", struct.fields)) +
        f") {{\n"
        f"\tif ({struct}_queue_empty(handle)) {{\n"
        f"\t\treturn false;\n"
        f"\t}}\n"
        f"\n"
        f"\t{struct}_queue_t *queue = handle->{struct}_queue;\n"
        f"\t{QUEUE_INDEX_TYPE} index = queue->head % 1 << handle->queue_capacity_bits;\n" +
        "".join(map(lambda field : f"\t*{field} = queue->element[index].{field};\n", struct.fields)) +
        f"\n"
        f"\tTHREAD_MEMORY_RELEASE();\n"
        f"\tqueue->head++;\n"
        f"\n"
        f"\treturn true;\n"
        f"}}\n"
        f"\n"
        )

if __name__ == '__main__':
    argparser = argparse.ArgumentParser('sDDF Queue C Codegenerator')
    argparser.add_argument('filename')
    argparser.add_argument('-o', '--output')
    argparser.add_argument('--comment',
                            action='store_true')
    args = argparser.parse_args()

    ast = pycparser.parse_file('test.h', use_cpp=True).children()
    
    # Strip irrelevant nesting
    ast = map(lambda node : node[1], ast)

    # Remove nodes not from specified file
    ast = filter(lambda node : node.coord.file == args.filename, ast)
    
    structs = list(map(_extract_struct, ast))
    assert(len(structs) > 0), \
        f"{args.filename} does not contain a struct"

    gen_comment = args.comment

    with sys.stdout if args.output == None else open(args.output, 'w') as output:
        for struct in structs:
            output.write(_gen_queue_struct(struct))
        output.write(_gen_queue_handle(structs))
        output.write(_gen_init_queue_handle(structs, gen_comment))
        for struct in structs:
            output.write(_gen_queue_empty(struct, gen_comment))
            output.write(_gen_queue_full(struct, gen_comment))
            output.write(_gen_queue_len(struct, gen_comment))
            output.write(_gen_enqueue(struct, gen_comment))
            output.write(_gen_dequeue(struct, gen_comment))

