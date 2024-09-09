#!/usr/bin/env python3

# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import os
import sys

from devicetree import edtlib, dtlib

if __name__ == "__main__":
    print("Creating a config file for clock driver to intialise the system...")

    print(sys.argv[0])
    print(sys.argv[1])

    devicetree = dtlib.DT(sys.argv[1], force=True)
