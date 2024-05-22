let
    pkgs = import <nixpkgs> {};
    llvm = pkgs.llvmPackages_18;
in
  pkgs.mkShell {
    buildInputs = with pkgs.buildPackages; [
        qemu
        gnumake
        llvm.clang
        llvm.lld
        llvm.libllvm
    ];
    # Nix will automatically add flags to Clang that depend
    # on OS functionality we do not provide (e.g stack protection).
    hardeningDisable = [ "all" ];
}

