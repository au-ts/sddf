"""
Converts all files in a folder with fio traces to C headers.
Compatible with fio I/O traces v3: https://fio.readthedocs.io/en/latest/fio_doc.html#trace-file-format . To write I/O traces with fio, see 'write_iolog' job file parameter.
Assumes the following file format:
    [benchmark_type]_[request_size][unit]

For example, for a random write, with single request size of 2 MiB:
    randomwrite_2M

The program will always output a single header file: 'converted_benchmark_traces.h', with 4 2D arrays of request offsets, 1 for each of the following: random read, random write, sequential read, sequential write.
NOTE: the request offsets are in terms of the sDDF defined include/sddf//blk/queue.h: BLK_TRANSFER_SIZE."""
import argparse
import os
from datetime import datetime, UTC
#from os import listdir

SD_PHYSICAL_BLOCK_SIZE = 512
SDDF_BLK_TRANSFER_SIZE = 4096
SUPPORTED_BENCHMARKS = ["randomread", "randomwrite", "read", "write"]
SUPPORTED_UNITS = ["K", "M", "G", "T"]

c_header_string = f"/*\n* Generated on: {datetime.now(UTC)} (UTC).\n* Generated with " \
        "fio_trace2cheader.py\n*/\n"
c_header_string += "#include <stdint.h>\n\n"
random_read_traces = {}
random_write_traces = {}
sequential_read_traces = {}
sequential_write_traces = {}


def get_trace_dict(benchmark_type: str) -> dict:
    """
    Map string name for the benchmark run type to the global dict accumulating
    all offsets for that run. Returns a reference to the appropriate dictionary.
    """
    if benchmark_type == "randomread":
        return random_read_traces
    elif benchmark_type == "randomwrite":
        return random_write_traces
    elif benchmark_type == "read":
        return sequential_read_traces
    elif benchmark_type == "write":
        return sequential_write_traces
    else:
        raise Exception("Whoops! something went wrong with validation!")


def validate_filename(file: str) -> None:
    """
    Exits if trace filename is not matching the required standard.
    """
    if len(file.split("_")) != 2:
        raise Exception(f"File {file} not in the expected format [benchmark_type]_[request_size][unit].")
    if file.split("_")[0] not in SUPPORTED_BENCHMARKS:
        raise Exception(f"File {file} not in the expected format [benchmark_type]_[request_size][unit].\n"
              f"Unrecognised benchmark type. Supported benchmarks: {SUPPORTED_BENCHMARKS}")
    if file.split("_")[1][-1] not in SUPPORTED_UNITS:
        raise Exception(f"File {file} not in the expected format [benchmark_type]_[request_size][unit].\n"
              f"Unrecognised request size unit. Supported units: {SUPPORTED_UNITS}")
    try:
        int(file.split("_")[1][:-1])
    except ValueError:
        raise Exception(f"File {file} not in the expected format [benchmark_type]_[request_size][unit].\n"
              f"Request size not an integer.")

def append_traces_to_write(random_read_traces: dict, benchmark_name: str) -> None:
    """
    Extends the c_header_string string with a 2D array definition of block offsets for
    replaying the trace.
    """
    global c_header_string
    # XXX: for now, assume num request equal across all runs in a single benchmark_type
    num_requests = len(list(random_read_traces.values())[0])
    # Add request offset array for random_read benchmark_type
    c_header_string += f"const uint32_t {benchmark_name}_OFFSETS_ARR[][{num_requests}] = {{\n" 
    for req_size in sorted(random_read_traces.keys()):
        c_header_string += f"// Size: {req_size//4096} blk transfers, count: {num_requests}\n"
        c_header_string += "{"
        c_header_string += repr(random_read_traces[req_size])[1:-1]
        c_header_string += "},\n"
    c_header_string += "};\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
            prog="Accepts a folder of FIO  I/O traces v3. File naming convention: [benchmark_type]_[request_size][unit]. Returns a single header file: 'converted_benchmark_traces.h' to be included by client.c and used to replay same workloads as Linux."
                        )
    parser.add_argument("--fio-traces-folder", help="path to traces of fio runs.", required=True)

    args = parser.parse_args()

    assert os.path.exists(args.fio_traces_folder)
    trace_files = os.listdir(args.fio_traces_folder)
    print(trace_files)
    for file in trace_files:
        # validate filename
        validate_filename(file)
        benchmark_type = file.split("_")[0]
        size_with_unit = file.split("_")[1]
        trace_dict = get_trace_dict(benchmark_type)
        # XXX: Currently assumes all requests are same size, gets the size of request from first req in the trace
        # For mixed request size workloads, may need to track a separate array for the request sizes
        request_size_bytes = None

        with open(os.path.join(args.fio_traces_folder, file), 'r') as f:
            fio_version = f.readline()
            # minimally validate file contents
            if fio_version != "fio version 3 iolog\n":
                raise Exception(f"First line of {file} is not 'fio version 3 iolog', but: '{fio_version}'")
            for line in f.readlines():
                # only keep lines that contain read or write commands
                if not any(x in line for x in ("read", "write")):
                    continue
                if request_size_bytes is None:
                    # Update request_size_bytes on the first valid read/write request, assumes all are equal size
                    request_size_bytes = int(line.split(" ")[4])
                offset_bytes = int(line.split(" ")[3])
                assert offset_bytes % SDDF_BLK_TRANSFER_SIZE == 0, f"FIO offset for request: '{line}' in file: {file} is not aligned to SDDF_BLK_TRANSFER_SIZE: {SDDF_BLK_TRANSFER_SIZE}. sDDF requires write/read request alignment to SDDF_BLK_TRANSFER_SIZE."
                offset = offset_bytes // SDDF_BLK_TRANSFER_SIZE
                try:
                    trace_dict[request_size_bytes].append(offset)
                except KeyError:
                    trace_dict[request_size_bytes] = [offset]
            print(f"{benchmark_type}: request size: {size_with_unit} [{request_size_bytes}B], num_requests: {len(trace_dict[request_size_bytes])}")

    # XXX: assume all benchmarks are same length
    assert len(random_read_traces) == len(random_write_traces) == len(sequential_read_traces) \
            == len(sequential_write_traces), "Not all traces have the same number of runs."
    # TODO: extract benchmark sizes and write a #define BENCHMARK_BLOCKS_PER_REQUEST (in terms of 4096 BLK_TRANSFER_SIZE)
    # TODO: extract request counts for each size (assume equal across all benchmark types, can validate), and define a #define REQUEST_COUNT array

    #c_header_string += f"#define REQUEST_COUNT {ra}\n"
    append_traces_to_write(random_read_traces, "RANDOM_READ")
    append_traces_to_write(random_write_traces, "RANDOM_WRITE")
    append_traces_to_write(sequential_read_traces, "SEQUENTIAL_READ")
    append_traces_to_write(sequential_write_traces, "SEQUENTIAL_WRITE")

    with open("include/benchmark_config/benchmark_traces.h", "w") as f:
        f.write(c_header_string)

