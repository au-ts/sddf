#!/usr/bin/env python3

import csv
import collections
import string
import sys

def process_core(n: int, part: str):
    parts = part.split("Utilisation details for")
    for x in parts[1:]:
        assert "PD: " in x

    ret = {}

    totals = parts[0]
    for line in totals.split("\n"):
        if ": " not in line: continue

        first, last = line.split(": ")
        ret[first.strip()] = int(last.strip())

    # print("   ", ret)
    assert len(ret.keys()) == 10 or len(ret.keys()) == 11
    return ret

inp = sys.argv[1]
oup = inp + ".summary.csv"
with open(inp, "r") as f:
    contents = f.read()

    summary = []
    parts_core = []
    num_cores = -1

    for part in contents.split("{CORE ")[1:]:
        core = string.digits.index(part[0])

        v = process_core(core, part[2:])
        if core == 0:
            if len(parts_core) != 0:
                summary.append(parts_core)
                if num_cores == -1:
                    num_cores = len(parts_core)
                else:
                    assert num_cores == len(parts_core)
                parts_core = []

        parts_core.append(v)

    assert len(parts_core) != 0
    summary.append(parts_core)

    print(num_cores)
    # print(summary)

with open(oup, "w", newline="") as f:
    writer = csv.DictWriter(f, delimiter=",", fieldnames=summary[0][0].keys())
    writer.writeheader()
    for bench in summary:
        totals = collections.defaultdict(int)
        for core in bench:
            for k, v in core.items():
                totals[k] += v

        writer.writerow(totals)
