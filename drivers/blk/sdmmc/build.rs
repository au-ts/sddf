fn main() {
    // Specify the path where the C library is located
    println!("cargo:rustc-link-search=native=./");

    // Link the C library (static or dynamic). Adjust "static" or "dylib" as needed.
    println!("cargo:rustc-link-lib=static=sddfblk");
}
