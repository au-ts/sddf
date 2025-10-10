#!/usr/bin/env python3

# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import socket
import sys

UDP_ECHO_PORT = 1235
TCP_ECHO_PORT = 1237


def udp(ip: str) -> bool:
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    server_port = UDP_ECHO_PORT
    s.connect((ip, server_port))
    message = "Hello World"
    s.send(message.encode())
    response = s.recv(1024).decode()

    return message == response


def tcp(ip: str) -> bool:
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_port = TCP_ECHO_PORT
    s.connect((ip, server_port))
    message = "Hello World"
    s.send(message.encode())
    response = s.recv(1024).decode()

    return message == response


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("ip")
    args = parser.parse_args()

    if udp(args.ip):
        print("SUCCESS: Received UDP response")
    else:
        print("ERROR: UDP failed")

    if tcp(args.ip):
        print("SUCCESS: Received TCP response")
    else:
        print("ERROR: TCP failed")
