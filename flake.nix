#
# Copyright 2024, UNSW
# SPDX-License-Identifier: BSD-2-Clause
#
{
  description = "A flake for building sDDF";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    systems-ci.url = "github:au-ts/systems-ci/main";
    systems-ci.flake = false;
    acacia.url = "github:au-ts/microkit_acacia/1.0";
    acacia.flake = false;
  };

  outputs =
    {
      nixpkgs,
      systems-ci,
      acacia,
      ...
    }:
    let
      microkit-version = "2.4.0";
      microkit-url = "https://github.com/seL4/microkit/releases/download/2.4.0/";
      microkit-platforms = {
        aarch64-darwin = "macos-aarch64";
        x86_64-darwin = "macos-x86-64";
        x86_64-linux = "linux-x86-64";
        aarch64-linux = "linux-aarch64";
      };

      forAllSystems = with nixpkgs.lib; genAttrs (builtins.attrNames microkit-platforms);
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };

          llvm = pkgs.llvmPackages_18;

          mk_acacia = pkgs.callPackage "${acacia}/package.nix" {
            python3Packages = pkgs.python312Packages;
          };

          clang-complete = (pkgs.symlinkJoin {
            name = "clang-complete";
            paths = [ llvm.clang-unwrapped.out llvm.clang-unwrapped.lib llvm.clang-unwrapped.python ];
            meta.mainProgram = "clang";

            # Clang searches up from the directory where it sits to find its built-in
            # headers. The `symlinkJoin` creates a symlink to the clang binary, and that
            # symlink is what ends up in your PATH from this shell. However, that symlink's
            # destination, the clang binary file, still resides in its own nix store
            # entry (`llvm.clang-unwrapped`), isolated from the header files (found in
            # `llvm.clang-unwrapped.lib` under `lib/clang/18/include`). So when search up its
            # parent directories, no built-in headers are found.
            #
            # By copying over the clang binary over the symlinks in the realisation of the
            # `symlinkJoin`, we can fix this; now the search mechanism looks up the parent
            # directories of the `clang` binary (which is a copy created by below command),
            # until it finds the aforementioned `lib/clang/18/include` (where the `lib` is
            # actually a symlink to `llvm.clang-unwrapped.lib + "/lib"`).
            postBuild = ''
              cp --remove-destination -- ${llvm.clang-unwrapped}/bin/* $out/bin/
            '';
          });

          # pancake/cakeml compiler
          pancake = pkgs.callPackage ./ci/cakeml.nix { };

          genmc = pkgs.callPackage ./ci/genmc/nix/package.nix { inherit clang-complete; llvm = pkgs.llvmPackages_20.llvm; };

          pythonTool = pkgs.python312.withPackages (ps: [
            mk_acacia
          ]);
        in
        {
          genmc = pkgs.mkShell rec {
            nativeBuildInputs = [
              genmc
            ];
          };

          spin-models = pkgs.mkShell {
            nativeBuildInputs = with pkgs; [
              spin
              gcc
            ];
          };

          # For building the design document
          docs = pkgs.mkShell rec {
            nativeBuildInputs = with pkgs; [
              texliveFull
              gnumake
              inkscape
              gnuplot
              which
            ];
          };
          # Shell for developing sDDF.
          # Includes dependencies for building sDDF and its examples.
          # mkShellNoCC, because we do not want the cc from stdenv to leak into this shell
          default = pkgs.mkShellNoCC rec {
            name = "sddf-dev";

            microkit-platform = microkit-platforms.${system} or (throw "Unsupported system: ${system}");

            env.MICROKIT_SDK = pkgs.fetchzip {
              url = "${microkit-url}/microkit-sdk-${microkit-version}-${microkit-platform}.tar.gz";
              hash =
                {
                  aarch64-darwin = "sha256-OOc20qE7HmNXKvdY77AeI2x5Lts29E3lety1nJuomxM=";
                  x86_64-darwin = "sha256-FZvaFv97Q/md8QqGDpmFVlRGYdDqjw48mbgdGr6C/ks=";
                  aarch64-linux = "sha256-z8L1eTmqLs6acwf25Wj4X3VkCuP2gVBMAo+B1OVDXiw=";
                  x86_64-linux = "sha256-FrSMQgjeW5Zox2JsNWa2Zme+gjv9d3ISXVbyBfnEqlI=";
                }
                .${system} or (throw "Unsupported system: ${system}");
            };

            nativeBuildInputs = with pkgs; [
              qemu
              gnumake
              dosfstools
              imagemagick
              # for shasum
              perl
              which
              gptfdisk
              clang-complete
              # for git-clang-format.
              llvm.libclang.python
              llvm.lld
              llvm.libllvm
              dtc
              pythonTool
              pancake
            ];

            # To avoid Nix adding compiler flags that are not available on a freestanding
            # environment.
            hardeningDisable = [ "all" ];
          };
        }
      );
    };
}
