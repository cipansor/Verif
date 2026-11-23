#!/bin/sh
# C8 external-crate demo: verify a function in a `no_std` crate that depends on a
# real crates.io crate (`embedded-hal`), end to end with `cargo verif`.
#
# The mechanism is the one the path-dependency fixtures exercise, on a crate the
# repository does not control: the crate `use`s `embedded_hal`, so the frontend's
# single-file `rustc` run needs `--extern embedded_hal`, which `crate_options`
# resolves from the built dependency.
#
# Exit codes, matching the other tools/: 0 the demo held (a true contract verified
# and a false one refuted), 1 a verdict was wrong, 2 the demo could not run (no
# cargo, or no network to fetch `embedded-hal`). A skip is reported, never passed.
set -u

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="$HOME/.cargo/bin:$PATH"

command -v cargo >/dev/null 2>&1 || { echo "external-demo: no cargo; skipping"; exit 2; }

BIN="$ROOT/target/debug/cargo-verif"
if [ ! -x "$BIN" ]; then
    ( cd "$ROOT" && cargo build -q --features std --bin cargo-verif ) \
        || { echo "external-demo: could not build cargo-verif"; exit 2; }
fi

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

write_crate() {
    dir=$1
    body=$2
    mkdir -p "$dir/src"
    cat > "$dir/Cargo.toml" <<'TOML'
[package]
name = "extdemo"
version = "0.0.0"
edition = "2024"

[dependencies]
embedded-hal = "=1.0.0"
TOML
    printf '%s\n' "$body" > "$dir/src/lib.rs"
}

TRUE_BODY='#![no_std]
use embedded_hal::digital::OutputPin;

/// requires: value <= 100
/// ensures: ret <= 100
pub fn clamp_percent(value: u16) -> u16 {
    if value > 100 { 100 } else { value }
}

pub fn drive<P: OutputPin>(pin: &mut P) -> Result<(), P::Error> {
    pin.set_high()
}'

FALSE_BODY='#![no_std]
use embedded_hal::digital::OutputPin;

/// ensures: ret == 7
pub fn wrong(value: u16) -> u16 { value }

pub fn drive<P: OutputPin>(pin: &mut P) -> Result<(), P::Error> {
    pin.set_high()
}'

ok=1
for name in true false; do
    d="$WORK/$name"
    if [ "$name" = true ]; then write_crate "$d" "$TRUE_BODY"; else write_crate "$d" "$FALSE_BODY"; fi
    ( cd "$d" && cargo build -q ) >/dev/null 2>&1 \
        || { echo "external-demo: could not fetch/build embedded-hal (no network?)"; exit 2; }
    out=$("$BIN" --file "$d/src/lib.rs" 2>&1)
    code=$?
    if [ "$name" = true ]; then
        if [ "$code" -eq 0 ] && printf '%s' "$out" | grep -q "verified"; then
            echo "external-demo: true contract verified (exit 0)"
        else
            echo "external-demo: TRUE CONTRACT NOT VERIFIED (exit $code)"
            printf '%s\n' "$out"
            ok=0
        fi
    else
        if [ "$code" -eq 1 ] && printf '%s' "$out" | grep -q "FAILED"; then
            echo "external-demo: false contract refuted (exit 1)"
        else
            echo "external-demo: FALSE CONTRACT NOT REFUTED (exit $code)"
            printf '%s\n' "$out"
            ok=0
        fi
    fi
done

if [ "$ok" -eq 1 ]; then
    echo "external-demo: OK"
    exit 0
fi
exit 1
