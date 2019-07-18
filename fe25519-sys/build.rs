extern crate bindgen;
extern crate cc;

use std::path::PathBuf;

const FE25519_SRCS: [&str; 12] = [
    "fe25519/bigint.c",
    "fe25519/cortex_m4_fe25519_mpy_uint16.S",
    "fe25519/cortex_m4_mpy121666.S",
    "fe25519/cortex_m4_mpy_192.S",
    "fe25519/cortex_m4_mpy_256.S",
    "fe25519/cortex_m4_mpy_fe25519.S",
    "fe25519/cortex_m4_reduce25519.S",
    "fe25519/cortex_m4_sqr_256.S",
    "fe25519/cortex_m4_sqr_fe25519.S",
    "fe25519/fe25519.c",
    "fe25519/fe25519_constants.c",
    "fe25519/fe25519_invert.c",
];

fn main() {
    cc::Build::new()
        .files(&FE25519_SRCS)
        .define("CRYPTO_HAS_ASM_FE25519_ADD", None)
        .define("CRYPTO_HAS_ASM_FE25519_SUB", None)
        .define("CRYPTO_HAS_ASM_FE25519_MUL", None)
        .define("CRYPTO_HAS_ASM_FE25519_SQUARE", None)
        .define("CRYPTO_HAS_ASM_REDUCE_25519", None)
        .define("CORTEX_M4", None)
        .compile("fe25519");
    println!("cargo:rustc-link-lib=fe25519");

    // Generate the bindings to fe25519
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .use_core()
        .ctypes_prefix("crate::c_types")
        .whitelist_function("fe25519_add_asm")
        .whitelist_function("fe25519_cmov")
        .whitelist_function("fe25519_cpy")
        .whitelist_function("fe25519_cswap")
        .whitelist_function("fe25519_getparity")
        .whitelist_function("fe25519_invert")
        .whitelist_function("fe25519_iseq_vartime")
        .whitelist_function("fe25519_iszero")
        .whitelist_function("fe25519_mpyWith_uint16_asm")
        .whitelist_function("fe25519_mul_asm")
        .whitelist_function("fe25519_neg")
        .whitelist_function("fe25519_one")
        .whitelist_function("shiftLeftOne")
        .whitelist_function("fe25519_pack")
        .whitelist_function("fe25519_reduceCompletely")
        .whitelist_function("fe25519_reduceTo256Bits_asm")
        .whitelist_function("fe25519_setone")
        .whitelist_function("fe25519_setzero")
        .whitelist_function("fe25519_square_asm")
        .whitelist_function("fe25519_squareroot")
        .whitelist_function("fe25519_sub_asm")
        .whitelist_function("fe25519_unpack")
        .whitelist_function("fe25519_zero")
        .generate()
        .expect("Unable to generate fe25519 bindings.");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
