# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause
let
    nixpkgs =
        let rev = "345c263f2f53a3710abe117f28a5cb86d0ba4059";
        in builtins.fetchTarball {
            name = "source";
            url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
            sha256 = "sha256:1llzyzw7a0jqdn7p3px0sqa35jg24v5pklwxdybwbmbyr2q8cf5j";
        };

    pkgs = import nixpkgs {};
    llvm = pkgs.llvmPackages_19;
in
  pkgs.mkShell {
    packages = with pkgs; [
        qemu
        gnumake
        llvm.clang
        llvm.lld
        llvm.libllvm
        dosfstools

        # for git-clang-format. nix is weird.
        llvm.libclang.python
    ];

    # Nix will automatically add flags to Clang that depend
    # on OS functionality we do not provide (e.g stack protection).
    hardeningDisable = [ "all" ];
}
