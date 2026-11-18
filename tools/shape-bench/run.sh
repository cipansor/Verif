#!/bin/sh
# Print the table the README's "Two ways to use the verifier" section quotes.
#
# Four crates share one piece of business logic and one driver; only the way
# verification is attached differs:
#
#   no_verif      -- the baseline: nothing of `verif` in the build.
#   build_verif   -- `verif` in `[build-dependencies]`, called from `build.rs`.
#                    Verification happens at compile time; the artifact is clean.
#   runtime_verif -- `verif` a normal dependency, its engine called from the
#                    crate's own code. The decision procedure is *in* the binary
#                    and runs at run time, discharging the *same* obligation the
#                    build-time crate proves.
#   unused_verif  -- `verif` a normal dependency, never called. The linker drops
#                    it, which is why the binary is the baseline again -- and why
#                    "a dependency you never call costs nothing" is not a proof.
#
# It reports, per crate: compile wall/CPU/peak-RSS (cold, `cargo clean`), binary
# size and `verif` symbol count, and the run-time wall/CPU/peak-RSS of the binary.
# It also prints the engine's in-process per-proof cost, which is the figure the
# README quotes for "one obligation". The numbers are what the README quotes; run
# this and compare rather than trusting the prose.
#
# The runtime workload is the *real* obligation, not a tautology: the on-target
# driver builds `ite(x > 100, 100, x) <= 100` at 32 bits -- the bound of the
# shared `clamp100` -- and proves it with the embedded engine. An earlier version
# proved `x < 65536 || x >= 65536` on a 16-bit variable, which folds to `true`
# (`lt_val` on a constant at or above the maximum is constant true, `ge_val`
# constant false), so the solver was handed no symbolic obligation at all and the
# reported run time excluded the verification. This one discharges a real bound.
#
# Measurement is done by `tools/shape-bench/measurer.rs` (built here with rustc),
# not by a Python `wait4`: `fork` from Python puts Python's own ~5 MB RSS under
# every figure, which is invisible on a ~500 MB build and dominant on a 2 MB run.
# See the launcher's header for the full reasoning.
#
# This is deliberately *not* a gate. A gate's job is to fail when something is
# wrong; this is a measurement whose numbers move with the machine, and a CI job
# that asserted them would fail on a slower runner for a reason that has nothing
# to do with the crate. `tools/build-verify/run.sh` (gate 18) is the *checked*
# half -- it asserts the two properties (verification at build time, no prover in
# the artifact) rather than reporting their cost.
#
# Exit status: 0 the table was printed; 2 no cargo/rustc, so nothing was measured.
#
# Usage: sh tools/shape-bench/run.sh
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"   # .../tools/shape-bench
ROOT="$(cd "$HERE/../.." && pwd)"        # the repository root
cd "$ROOT"

if ! command -v cargo >/dev/null 2>&1; then
  echo "shape-bench: no cargo on PATH, so nothing was measured" >&2
  exit 2
fi
if ! command -v rustc >/dev/null 2>&1; then
  echo "shape-bench: no rustc on PATH, so nothing was measured" >&2
  exit 2
fi

ROOT="$(pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT INT TERM

# The native launcher: `-t` for a build (sample the whole tree, report the largest
# single process), no flag for a run (sample the one child).
MEASURER="$WORK/measurer"
rustc -O --edition 2024 -o "$MEASURER" "$HERE/measurer.rs"

# One business function with a contract the MIR frontend can verify, and one
# driver that exercises it. Both are shared verbatim by every crate.
cat > "$WORK/shared_lib.rs" <<'EOF'
/// requires: n <= 1_000_000
/// ensures: ret <= 100
pub fn clamp100(n: u32) -> u32 {
    if n > 100 { 100 } else { n }
}
EOF

cat > "$WORK/shared_main.rs" <<'EOF'
use bench_logic::clamp100;

fn main() {
    let mut s = 0u64;
    for i in 0..2_000_000u32 {
        s = s.wrapping_add(clamp100(i % 200) as u64);
    }
    std::hint::black_box(s);
}
EOF

cat > "$WORK/runtime_main.rs" <<'EOF'
use bench_logic::clamp100;
use verif::prelude::*;

fn main() {
    let mut s = 0u64;
    for i in 0..2_000_000u32 {
        s = s.wrapping_add(clamp100(i % 200) as u64);
    }
    std::hint::black_box(s);

    // The same bound the build-time crate proves of the body, discharged here at
    // run time by the decision procedure compiled into this binary: the clamped
    // result is always <= 100, for every u32 input.
    let ok = verif::smt::with_fresh(|| {
        let x = var(32);
        let clamped = verif::smt::ite(x.gt_val(100), verif::smt::word(100, 32), x);
        clamped.le_val(100).prove().is_proved()
    });
    assert!(ok, "clamp100's bound did not discharge");
    println!("runtime proof: bound <= 100 discharged");
}
EOF

# A fourth driver: the engine's in-process per-proof cost, which is what the
# README quotes for "one obligation". A single process, 1000 repetitions, so the
# figure is the proof and not process start-up.
cat > "$WORK/perproof_main.rs" <<'EOF'
use verif::prelude::*;
use std::time::Instant;

fn main() {
    let prove = || {
        verif::smt::with_fresh(|| {
            let x = var(32);
            let clamped = verif::smt::ite(x.gt_val(100), verif::smt::word(100, 32), x);
            clamped.le_val(100).prove().is_proved()
        })
    };
    for _ in 0..100 { std::hint::black_box(prove()); }
    let n = 1000u32;
    let t = Instant::now();
    let mut acc = 0u32;
    for _ in 0..n {
        if prove() { acc += 1; }
    }
    std::hint::black_box(acc);
    let us = t.elapsed().as_secs_f64() * 1e6 / n as f64;
    println!("{us:.2}");
}
EOF

mk_crate() {
  name="$1"; kind="$2"
  mkdir -p "$WORK/$name/src"
  {
    echo '[package]'
    echo "name = \"bench_$name\""
    echo 'version = "0.1.0"'
    echo 'edition = "2021"'
    echo
    echo '[lib]'
    echo 'name = "bench_logic"'
    echo 'path = "src/lib.rs"'
    echo
    echo '[[bin]]'
    echo "name = \"bench_$name\""
    echo 'path = "src/main.rs"'
    case "$kind" in
      build)   printf '\n[build-dependencies]\nverif = { path = "%s", features = ["std"] }\n' "$ROOT" ;;
      runtime) printf '\n[dependencies]\nverif = { path = "%s", features = ["std"] }\n' "$ROOT" ;;
    esac
  } > "$WORK/$name/Cargo.toml"
  cp "$WORK/shared_lib.rs" "$WORK/$name/src/lib.rs"
  cp "$WORK/shared_main.rs" "$WORK/$name/src/main.rs"
}

mk_crate no_verif none
mk_crate build_verif build
mk_crate runtime_verif runtime
mk_crate unused_verif runtime

cat > "$WORK/build_verif/build.rs" <<'EOF'
fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    let report = verif::mir::verify::verify_file_with("rustc", "src/lib.rs".as_ref(), &[])
        .expect("verif: the MIR frontend could not read the source");
    for (name, outcome) in &report.outcomes {
        println!("cargo:warning=verif {name}: {outcome}");
        assert!(outcome.is_verified(), "verif: {name} is not verified: {outcome}");
    }
}
EOF
cp "$WORK/runtime_main.rs" "$WORK/runtime_verif/src/main.rs"
# The unused crate keeps the runtime manifest but never calls the engine: `main`
# is the plain driver, so `verif` is linked and dropped.
cp "$WORK/shared_main.rs" "$WORK/unused_verif/src/main.rs"

echo "host: $(uname -sm), rustc $(rustc --version | awk '{print $2}')"
echo

# Fields from the launcher: code wall_s cpu_s peak_kb sampled
read_measure() {  # $1 = launcher flag (may be empty), rest = command
  flag="$1"; shift
  if [ -n "$flag" ]; then "$MEASURER" "$flag" "$@"; else "$MEASURER" "$@"; fi
}

echo "=== compile time (cold build, cargo clean; release) ==="
printf '%-14s %3s %9s %9s %12s %12s %8s\n' crate ok wall_s cpu_s peakRSS_MB bin_bytes verif_syms
for c in no_verif build_verif runtime_verif unused_verif; do
  d="$WORK/$c"
  ( cd "$d" && cargo clean >/dev/null 2>&1 )
  out=$(cd "$d" && read_measure -t cargo build --release)
  code=$(echo "$out" | cut -f1)
  wall=$(echo "$out" | cut -f2)
  cpu=$(echo "$out" | cut -f3)
  peak=$(echo "$out" | cut -f4)
  sampled=$(echo "$out" | cut -f5)
  # The launcher discards the child's stderr, so a build that *fails* still
  # returns a (tiny) wall time. Treat a non-zero exit or a missing binary as a
  # failed row rather than printing a fast-looking 0.04 s: a measurement of a
  # build that did not happen is the worst output a benchmark can give.
  bin=$(find "$d/target/release" -maxdepth 1 -name "bench_*" -type f -perm -u+x | head -n1 || true)
  if [ "$code" != "0" ] || [ -z "$bin" ]; then
    printf '%-14s FAILED (exit %s, no binary; re-run with MEASURER_SHOW_CHILD=1 to see cargo)\n' "$c" "$code" >&2
    exit 1
  fi
  if [ "$sampled" = "0" ]; then rssmb="(short)"; else
    rssmb=$(awk -v k="$peak" 'BEGIN{printf "%.1f", k/1024}')
  fi
  size=$(wc -c < "$bin" | tr -d ' ')
  syms="n/a"
  if command -v nm >/dev/null 2>&1; then
    syms=$(nm -C "$bin" 2>/dev/null | grep -cE '(^|[^_A-Za-z0-9])verif::' || true)
  fi
  printf '%-14s %3s %9s %9s %12s %12s %8s\n' "$c" "$code" "$wall" "$cpu" "$rssmb" "$size" "$syms"
done

echo
echo "=== run time (7 runs each; median wall/cpu, peak RSS) ==="
printf '%-14s %10s %10s %12s\n' crate wall_s cpu_s peakRSS_MB
for c in no_verif build_verif runtime_verif unused_verif; do
  bin=$(find "$WORK/$c/target/release" -maxdepth 1 -name "bench_*" -type f -perm -u+x | head -n1 || true)
  if [ -z "$bin" ]; then printf '%-14s  (no binary)\n' "$c"; continue; fi
  ws=""; cs=""; ps=""
  i=0
  while [ $i -lt 7 ]; do
    out=$(read_measure "" "$bin")
    ws="$ws $(echo "$out" | cut -f2)"
    cs="$cs $(echo "$out" | cut -f3)"
    ps="$ps $(echo "$out" | cut -f4)"
    i=$((i+1))
  done
  med_w=$(printf '%s\n' $ws | sort -n | sed -n '4p')
  med_c=$(printf '%s\n' $cs | sort -n | sed -n '4p')
  max_p=$(printf '%s\n' $ps | sort -n | sed -n '7p')
  rssmb=$(awk -v k="$max_p" 'BEGIN{printf "%.1f", k/1024}')
  printf '%-14s %10s %10s %12s\n' "$c" "$med_w" "$med_c" "$rssmb"
done

echo
echo "=== engine cost, one obligation (32-bit ite(x>100,100,x) <= 100) ==="
# A separate crate so the run-time crate's own `main` stays the one measured above.
mkdir -p "$WORK/perproof/src"
cat > "$WORK/perproof/Cargo.toml" <<EOF
[package]
name = "bench_perproof"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "bench_perproof"
path = "src/main.rs"

[dependencies]
verif = { path = "$ROOT", features = ["std"] }
EOF
cp "$WORK/perproof_main.rs" "$WORK/perproof/src/main.rs"
if ! ( cd "$WORK/perproof" && cargo build --release >/dev/null 2>&1 ); then
  echo "shape-bench: the per-proof crate did not build" >&2
  exit 1
fi
us=$("$WORK/perproof/target/release/bench_perproof")
printf 'in-process, 1000 repetitions: %s us/proof\n' "$us"

echo
echo "note: the build-time crate's build-dependency is compiled with cargo's"
echo "build-override profile (opt-level 0 by default), so its compile figures are"
echo "not directly comparable to the run-time crate's, whose dependency is compiled"
echo "at the release profile's opt-level. Set [profile.release.build-override]"
echo "opt-level = 3 to compare like with like -- the wall time then matches."
