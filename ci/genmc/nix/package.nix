#
# Copyright 2025, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
{
  fetchFromGitHub,
  stdenv,
  lib,
  llvm,
  clang,
  clang-complete,
  cmake,
  pkg-config,
  libxml2,
  libffi,
}:
stdenv.mkDerivation (rec {
  pname = "genmc";
  version = "v0.13.0";
  src = fetchFromGitHub {
    owner = "MPI-SWS";
    repo = "genmc";
    rev = version;
    hash = "sha256-a+ZhzuKmhLem8ScCKI1EW8KTy+UuhmzU1Vt8y+NzS8c=";
  };

  nativeBuildInputs = [
    cmake
    libxml2
    pkg-config
    llvm
    clang
    libffi
  ];

  buildInputs = [
    clang-complete
  ];

  cmakeFlags = [
    "-DLLVM_CONFIG_PATH=llvm-config"
    "-DCLANGPATH=${lib.getExe clang-complete}"
  ];

  patches = [
    ./cmake_install.patch
  ];
})
