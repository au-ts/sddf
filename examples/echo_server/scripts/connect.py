#!/usr/bin/env python3

# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause

import argparse
import socket
import sys

UDP_ECHO_PORT = 1235
TCP_ECHO_PORT = 1236


def udp(ip: str):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    server_port = UDP_ECHO_PORT
    s.connect((ip, server_port))
    message = "Hello World"
    s.send(message.encode())
    response = s.recv(1024).decode()
    print("SUCCESS: Received UDP response" if message == response else "UDP failed")


def tcp(ip: str):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_port = TCP_ECHO_PORT
    s.connect((ip, server_port))
    message = "Hello World"
    s.send(message.encode())
    response = s.recv(1024).decode()
    print("SUCCESS: Received TCP response" if message == response else "TCP failed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("ip")
    args = parser.parse_args()

    udp(args.ip)
    tcp(args.ip)
