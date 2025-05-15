#!/usr/bin/env python3
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
from .backends import OUTPUT

def info(s):
    OUTPUT.write("CI|INFO: " + s + "\n")

def error(s):
    OUTPUT.write("CI|ERROR: " + s + "\n")
