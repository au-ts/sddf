"""
Converts all files in a folder with fio traces to C headers.
Compatible with fio I/O traces v3: https://fio.readthedocs.io/en/latest/fio_doc.html#trace-file-format . To write I/O traces with fio, see 'write_iolog' job file parameter.
Assumes the following file format:
    [benchmark_type]_[request_size][unit]

For example, for a random write, with single request size of 2 MiB:
    randomwrite_2M

The program will always output a single header file: 'converted_benchmark_traces.h', with 4 2D arrays of request offsets, 1 for each of the following: random read, random write, sequential read, sequential write.
"""
import argparse
import os
#from os import listdir

SD_PHYSICAL_BLOCK_SIZE = 512
SUPPORTED_BENCHMARKS = ["randomread", "randomwrite", "read", "write"]
SUPPORTED_UNITS = ["K", "M", "G", "T"]

random_read_traces = {}
random_write_traces = {}
sequential_read_traces = {}
sequenital_write_traces = {}

def get_trace_dict(benchmark_type: str) -> dict:
    if benchmark_type == "randomread":
        return random_read_traces
    elif benchmark_type == "randomwrite":
        return random_write_traces
    elif benchmark_type == "read":
        return sequential_read_traces
    elif benchmark_type == "write":
        return sequenital_write_traces
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

        with open(os.path.join(args.fio_traces_folder, file), 'r') as f:
            fio_version = f.readline()
            # minimally validate file contents
            if fio_version != "fio version 3 iolog\n":
                raise Exception(f"First line of {file} is not 'fio version 3 iolog', but: '{fio_version}'")
            for line in f.readlines():
                # only keep lines that contain read or write commands
                if not any(x in line for x in ("read", "write")):
                    continue
                offset = int(line.split(" ")[3]) // SD_PHYSICAL_BLOCK_SIZE
                try:
                    trace_dict[size_with_unit].append(offset)
                except KeyError:
                    trace_dict[size_with_unit] = [offset]
            print(f"{benchmark_type}: request size: {size_with_unit}, num_requests: {len(trace_dict[size_with_unit])}")
        #print(trace_dict)

