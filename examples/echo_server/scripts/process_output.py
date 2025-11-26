#!/usr/bin/env python3

import sys
import re
import copy

if len(sys.argv) < 2 or len(sys.argv) > 3:
    print("usage: process_microkit_output output.log [comma_separated_throughput]")
    sys.exit()

# Test throughputs
test_string = [10, 20, 50, 100, 200, 300, 400, 500, 600, 700, 800, 900, 970]
if len(sys.argv) == 3:
    test_string = sys.argv[2].split(",")

# Number of cores on the board
num_cores = 4

# Data collected for each core and PD
data = {"total": 0, "kernel": 0, "user": 0, "entries": 0, "schedules": 0}

# Summed data collected for each core
core_data = {"pd_total": 0, "pd_kernel": 0, "pd_user": 0, "data": dict(data)}

# Named data for each PD
pd_data = {"name": "", "data": dict(data)}

# Global data structure to store all data collected in each test
test_data = {
    "test": 0,
    "active": 0,
    "cores": [copy.deepcopy(core_data) for _ in range(num_cores)],
    "pds": [[] for _ in range(num_cores)],
    "system": copy.deepcopy(core_data),
}

# Output of processing script
results_output = {
    "system": "Component,Core Cycles,System Cycles,Kernel Cycles,User Cycles,Kernel Entries,Schedules,Core CPU Util,Core Kernel CPU Util,Core User CPU Util",
    "cores": "",
}

# PMU data
pmu_data = {}

# Colour codes used by sDDF serial
colour_end = "\x1b[0m"
colour_codes = [
    colour_end,
    "\x1b[31m",
    "\x1b[32m",
    "\x1b[33m",
    "\x1b[34m",
    "\x1b[35m",
    "\x1b[36m",
]


# Remove colour codes
def no_colour(line):
    for code in colour_codes:
        no_colours = line.split(code)
        line = "".join(no_colours)
    return line


# Skip formatting and colour lines
def next_result(f):
    line = no_colour(next(f))
    while len(line) < 3:
        line = no_colour(next(f))
    return line


# Create a line of .csv results
def result_string(pd, tc, tu, k, u, e, s, ut, kut, uut):
    return f"\n{pd},{tc},{tu},{k},{u},{e},{s},{round(100 * ut, 2)},{round(100 * kut, 2)},{round(100 * uut, 2)}"


# Convert test results dictionary to .csv output
def output_and_reset():
    global test

    # Calculate user cycles and system totals, create results output
    for core in range(num_cores):

        # Skip cores with no pds
        if not len(test["pds"][core]):
            continue
        test["active"] += 1

        # Sum up cycles used by PDs
        for pd in test["pds"][core]:
            pd["data"]["user"] = pd["data"]["total"] - pd["data"]["kernel"]
            test["cores"][core]["pd_total"] += pd["data"]["total"]
            test["cores"][core]["pd_kernel"] += pd["data"]["kernel"]
            test["cores"][core]["pd_user"] += pd["data"]["user"]

        # Sum up core counts
        test["system"]["pd_total"] += test["cores"][core]["pd_total"]
        test["system"]["pd_kernel"] += test["cores"][core]["pd_kernel"]
        test["system"]["pd_user"] += test["cores"][core]["pd_user"]
        for key in test["system"]["data"].keys():
            test["system"]["data"][key] += test["cores"][core]["data"][key]

        # Create core total results output
        total_core_cycles = test["cores"][core]["data"]["total"]
        results_output["cores"] += result_string(
            "CORE " + str(core) + " TOTAL",
            total_core_cycles,
            test["cores"][core]["pd_total"],
            test["cores"][core]["pd_kernel"],
            test["cores"][core]["pd_user"],
            test["cores"][core]["data"]["entries"],
            test["cores"][core]["data"]["schedules"],
            test["cores"][core]["pd_total"] / total_core_cycles,
            test["cores"][core]["pd_kernel"] / total_core_cycles,
            test["cores"][core]["pd_user"] / total_core_cycles,
        )

        # Create core PDs result output
        for pd in test["pds"][core]:
            pd_total_util = pd["data"]["total"] / total_core_cycles
            if pd_total_util > 1:
                print(
                    f"Error - pd {pd["name"]} has CPU utilisation {pd_total_util} > 1"
                )
            results_output["cores"] += result_string(
                pd["name"],
                total_core_cycles,
                pd["data"]["total"],
                pd["data"]["kernel"],
                pd["data"]["user"],
                pd["data"]["entries"],
                pd["data"]["schedules"],
                pd_total_util,
                pd["data"]["kernel"] / total_core_cycles,
                pd["data"]["user"] / total_core_cycles,
            )

    # Create system totals results output
    total_board_cycles = test["system"]["data"]["total"]
    results_output["system"] += result_string(
        f"System Total {test_string[test["test"] - 1]}Mb/s",
        total_board_cycles,
        test["system"]["pd_total"],
        test["system"]["pd_kernel"],
        test["system"]["pd_user"],
        test["system"]["data"]["entries"],
        test["system"]["data"]["schedules"],
        test["active"] * test["system"]["pd_total"] / total_board_cycles,
        test["active"] * test["system"]["pd_kernel"] / total_board_cycles,
        test["active"] * test["system"]["pd_user"] / total_board_cycles,
    )

    # Reset test, keep test number
    test["active"] = 0
    test["cores"] = [copy.deepcopy(core_data) for _ in range(num_cores)]
    test["pds"] = [[] for _ in range(num_cores)]
    test["system"] = copy.deepcopy(core_data)


# Process log file
file = sys.argv[1]
test = dict(test_data)
current_core = 0
with open(file, "r") as f:
    for line in f:
        line = no_colour(line)

        # New benchmark started
        if re.match(".* measurement starting...", line):
            if test["test"] > 0:
                output_and_reset()
            test["test"] += 1
            results_output[
                "cores"
            ] += f"\n\nTEST {test["test"]}: {test_string[test["test"]-1]}Mb/s"
            continue

        # Benchmark has not started yet
        if test["test"] == 0:
            continue

        # Change core
        match_core = re.match("{CORE ([0-9]*):", line)
        if match_core:
            current_core = eval(match_core.group(1))
            line = next_result(f)

        # Capture core or PD utilisation details
        match_total = re.match("Total utilisation details:.*", line)
        match_pd = re.match("Utilisation details for PD: ([a-zA-Z _0-3]*) .*", line)
        if match_total or match_pd:
            if match_total:
                data = test["cores"][current_core]["data"]
            elif match_pd:
                test["pds"][current_core].append(copy.deepcopy(pd_data))
                test["pds"][current_core][-1]["name"] = match_pd.group(1)
                data = test["pds"][current_core][-1]["data"]
            line = next_result(f)
            data["kernel"] = int(line[19:-1])
            line = next_result(f)
            data["entries"] = int(line[15:-1])
            line = next_result(f)
            data["schedules"] = int(line[17:-1])
            line = next_result(f)
            data["total"] = int(line[18:-1])

        else:
            # Skip TCP output
            tcp_match = re.match("tcp_echo:.*", line)
            if tcp_match:
                continue

            # Capture PMU details
            match = re.match(r"([\d\w -]+): ([0-9A-F]+).*", line)
            if not match:
                continue

            pmu_key = match.group(1)
            pmu_value = match.group(2)
            if (
                "psci" not in pmu_key
                and "Model" not in pmu_key
                and "Load" not in pmu_key
            ):

                # Create PMU entry per test
                if pmu_key not in pmu_data:
                    pmu_data[pmu_key] = [int(pmu_value)]
                elif len(pmu_data[pmu_key]) == (test["test"] - 1):
                    pmu_data[pmu_key].append(int(pmu_value))
                else:
                    pmu_data[pmu_key][test["test"] - 1] += int(pmu_value)

# Output results from final test
if test["test"]:
    output_and_reset()

print(results_output["system"], end="")
print(results_output["cores"])

# Print PMU data
if pmu_data:
    # Print PMU keys
    print("\n", ",".join(pmu_data.keys()), sep="")
    for index in range(0, test["test"]):
        for key in pmu_data.keys():
            print(f"{pmu_data[key][index]},", end="")
        print("\n", end="")
