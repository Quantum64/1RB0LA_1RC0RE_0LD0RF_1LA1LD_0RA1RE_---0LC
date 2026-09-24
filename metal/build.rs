use std::{env, path::PathBuf, process::Command};

fn run(command: &mut Command) {
    assert!(
        command.status().expect("native compiler").success(),
        "native compilation failed"
    );
}
fn main() {
    assert_eq!(
        env::var("CARGO_CFG_TARGET_OS").unwrap(),
        "macos",
        "Metal requires macOS"
    );
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let gmp = "/opt/homebrew/opt/gmp";
    run(Command::new("clang++")
        .args([
            "-O3",
            "-std=c++17",
            "-fobjc-arc",
            "-fPIC",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-I/opt/homebrew/opt/gmp/include",
            "-c",
            "src/metal.mm",
            "-o",
        ])
        .arg(out.join("metal.o")));
    run(Command::new("ar")
        .arg("crs")
        .arg(out.join("libtm_metal.a"))
        .arg(out.join("metal.o")));
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-search=native={gmp}/lib");
    for library in [
        "static=tm_metal",
        "gmp",
        "c++",
        "framework=Metal",
        "framework=Foundation",
    ] {
        println!("cargo:rustc-link-lib={library}");
    }
    println!("cargo:rustc-link-arg=-Wl,-rpath,{gmp}/lib");
    println!("cargo:rerun-if-changed=src/metal.mm");
}
