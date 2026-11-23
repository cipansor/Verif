//! Bake a hash of the engine's sources into the binary (U7).
//!
//! The proof cache (`mir::cache`) keys a verdict on the MIR text, the source text,
//! the edition **and this hash**, so *any* change to the engine invalidates every
//! cached verdict. Without it a change to a budget or a rule could leave a stale
//! `verified` in the cache — a false proof, the one failure a verifier must not have.
//! The hash covers `src/**.rs` and `Cargo.toml`.
use std::fmt::Write as _;

fn main() {
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=Cargo.toml");
    let mut files: Vec<std::path::PathBuf> = Vec::new();
    collect(std::path::Path::new("src"), &mut files);
    files.push(std::path::PathBuf::from("Cargo.toml"));
    files.sort();
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for f in &files {
        if let Ok(bytes) = std::fs::read(f) {
            for b in bytes {
                h ^= b as u64;
                h = h.wrapping_mul(0x100_0000_01b3);
            }
        }
    }
    let mut s = String::new();
    let _ = write!(s, "{h:016x}");
    println!("cargo:rustc-env=VERIF_ENGINE_HASH={s}");
}

fn collect(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().map(|x| x == "rs").unwrap_or(false) {
            out.push(p);
        }
    }
}
