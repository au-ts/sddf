#!/usr/bin/env python3

# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import socket
import sys

UDP_ECHO_PORT = 1235
TCP_ECHO_PORT = 1236


def udp(ip: str, server_port: int):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect((ip, server_port))
    message = "Hello World"
    s.send(message.encode())
    response = s.recv(1024).decode()
    print("SUCCESS: Received UDP response" if message == response else "UDP failed")


def tcp(ip: str, server_port: int):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.connect((ip, server_port))
    message = "Hello World"
    s.send(message.encode())
    response = s.recv(1024).decode()
    print("SUCCESS: Received TCP response" if message == response else "TCP failed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("ip")
    parser.add_argument("--udp_port", required=False)
    parser.add_argument("--tcp_port", required=False)
    args = parser.parse_args()

    udp(args.ip, int(args.udp_port) if args.udp_port else UDP_ECHO_PORT)
    tcp(args.ip, int(args.tcp_port) if args.tcp_port else TCP_ECHO_PORT)
