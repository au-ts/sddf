#!/bin/bash

set -e

SDK_PATH=$1

# Number of threads/jobs to compile with, default to 1
if [ "$#" -eq 1 ]; then
NUM_JOBS=1
else
NUM_JOBS=$2
fi

CI_BUILD_DIR="ci_build"

[[ -z $SDK_PATH ]] && echo "usage: examples.sh [PATH TO SDK]" && exit 1
[[ ! -d $SDK_PATH ]] && echo "The path to the SDK provided does not exist: '$SDK_PATH'" && exit 1

build_network_echo_server() {
    CONFIG=$1
    BOARD=$2
    echo "CI|INFO: building echo server example with config: $CONFIG, board: $BOARD"
    BUILD_DIR="${PWD}/${CI_BUILD_DIR}/examples/echo_server/${BOARD}/${CONFIG}"
    rm -rf ${BUILD_DIR}
    mkdir -p ${BUILD_DIR}
    make -j${NUM_JOBS} -C examples/echo_server \
        BUILD_DIR=${BUILD_DIR} \
        MICROKIT_CONFIG=${CONFIG} \
        MICROKIT_SDK=${SDK_PATH} \
        MICROKIT_BOARD=${BOARD}
}

build_i2c() {
    CONFIG=$1
    echo "CI|INFO: building I2C example with config: $CONFIG"
    BUILD_DIR="${PWD}/${CI_BUILD_DIR}/examples/i2c/${CONFIG}"
    rm -rf ${BUILD_DIR}
    mkdir -p ${BUILD_DIR}
    make -j${NUM_JOBS} -C examples/i2c \
        BUILD_DIR=${BUILD_DIR} \
        MICROKIT_CONFIG=${CONFIG} \
        MICROKIT_SDK=${SDK_PATH}
}

build_timer() {
    CONFIG=$1
    echo "CI|INFO: building timer example with config: $CONFIG"
    BUILD_DIR="${PWD}/${CI_BUILD_DIR}/examples/timer/${CONFIG}"
    rm -rf ${BUILD_DIR}
    mkdir -p ${BUILD_DIR}
    make -j${NUM_JOBS} -C examples/timer \
        BUILD_DIR=${BUILD_DIR} \
        MICROKIT_CONFIG=${CONFIG} \
        MICROKIT_SDK=${SDK_PATH}
}

build_serial() {
    CONFIG=$1
    BOARD=$2
    echo "CI|INFO: building serial example with config: $CONFIG, board: $BOARD"
    BUILD_DIR="${PWD}/${CI_BUILD_DIR}/examples/serial//${BOARD}/${CONFIG}"
    rm -rf ${BUILD_DIR}
    mkdir -p ${BUILD_DIR}
    make -j${NUM_JOBS} -C examples/serial_two_client \
        BUILD_DIR=${BUILD_DIR} \
        MICROKIT_CONFIG=${CONFIG} \
        MICROKIT_SDK=${SDK_PATH} \
        MICROKIT_BOARD=${BOARD}
}

build_network_echo_server "debug" "imx8mm_evk"
build_network_echo_server "release" "imx8mm_evk"
build_network_echo_server "benchmark" "imx8mm_evk"
build_network_echo_server "debug" "odroidc4"
build_network_echo_server "release" "odroidc4"
build_network_echo_server "benchmark" "odroidc4"

build_i2c "debug"
build_i2c "release"

build_timer "debug"
build_timer "release"

build_serial "debug" "odroidc4"
build_serial "release" "odroidc4"
build_serial "debug" "qemu_arm_virt"
build_serial "release" "qemu_arm_virt"

echo ""
echo "CI|INFO: Passed all sDDF tests"
