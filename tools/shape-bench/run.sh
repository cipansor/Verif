#!/bin/sh
# Print the table the README's "Two ways to use the verifier" section quotes.
#
# Three crates share one piece of business logic and one driver; only the way
# verification is attached differs:
#
#   no_verif      -- the baseline: nothing of `verif` in the build.
#   build_verif   -- `verif` in `[build-dependencies]`, called from `build.rs`.
#                    Verification happens at compile time; the artifact is clean.
#   runtime_verif -- `verif` a normal dependency, its engine called from the
#                    crate's own code. The decision procedure is *in* the binary
#                    and runs at run time.
#
# It reports, per crate: compile wall time and CPU (cold, `cargo clean`), the peak
# RSS of the largest process in the build tree, the binary size, and the run-time
# wall/CPU/peak-RSS of the binary. The figures are what the README quotes; run
# this and compare rather than trusting the prose.
#
# This is deliberately *not* a gate. A gate's job is to fail when something is
# wrong; this is a measurement whose numbers move with the machine, and a CI job
# that asserts them would fail on a slower runner for a reason that has nothing to
# do with the crate. `tools/build-verify/run.sh` (gate 18) is the *checked* half --
# it asserts the two properties (verification at build time, no prover in the
# artifact) rather than reporting their cost.
#
# Exit status: 0 the table was printed; 2 no cargo/python3, so nothing was measured.
#
# Usage: sh tools/shape-bench/run.sh
set -eu
cd "$(dirname "$0")/../.."

if ! command -v cargo >/dev/null 2>&1; then
  echo "shape-bench: no cargo on PATH, so nothing was measured" >&2
  exit 2
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo "shape-bench: no python3 on PATH, so nothing was measured" >&2
  exit 2
fi

ROOT="$(pwd)"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT INT TERM

# One business function with a contract the MIR frontend can verify, and one
# driver that exercises it. Both are shared verbatim by all three crates.
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
use verif::sym::*;

fn main() {
    let mut s = 0u64;
    for i in 0..2_000_000u32 {
        s = s.wrapping_add(clamp100(i % 200) as u64);
    }
    std::hint::black_box(s);

    // The same obligation the build-time crate proves, discharged here at run time
    // by the decision procedure compiled into this binary.
    let ok = verif::smt::with_fresh(|| {
        let x = var(16);
        verif::smt::or(x.lt_val(65536), x.ge_val(65536)).prove()
    });
    assert!(ok.is_proved());
    println!("runtime proof: {ok}");
}
EOF

# ---- 1. no_verif ----
mkdir -p "$WORK/no_verif/src"
cat > "$WORK/no_verif/Cargo.toml" <<'EOF'
[package]
name = "bench_no_verif"
version = "0.1.0"
edition = "2021"

[lib]
name = "bench_logic"
path = "src/lib.rs"

[[bin]]
name = "bench_no_verif"
path = "src/main.rs"
EOF
cp "$WORK/shared_lib.rs" "$WORK/no_verif/src/lib.rs"
cp "$WORK/shared_main.rs" "$WORK/no_verif/src/main.rs"

# ---- 2. build_verif ----
mkdir -p "$WORK/build_verif/src"
cat > "$WORK/build_verif/Cargo.toml" <<EOF
[package]
name = "bench_build_verif"
version = "0.1.0"
edition = "2021"

[lib]
name = "bench_logic"
path = "src/lib.rs"

[[bin]]
name = "bench_build_verif"
path = "src/main.rs"

[build-dependencies]
verif = { path = "$ROOT", features = ["std"] }
EOF
cp "$WORK/shared_lib.rs" "$WORK/build_verif/src/lib.rs"
cp "$WORK/shared_main.rs" "$WORK/build_verif/src/main.rs"
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

# ---- 3. runtime_verif ----
mkdir -p "$WORK/runtime_verif/src"
cat > "$WORK/runtime_verif/Cargo.toml" <<EOF
[package]
name = "bench_runtime_verif"
version = "0.1.0"
edition = "2021"

[lib]
name = "bench_logic"
path = "src/lib.rs"

[[bin]]
name = "bench_runtime_verif"
path = "src/main.rs"

[dependencies]
verif = { path = "$ROOT", features = ["std"] }
EOF
cp "$WORK/shared_lib.rs" "$WORK/runtime_verif/src/lib.rs"
cp "$WORK/runtime_main.rs" "$WORK/runtime_verif/src/main.rs"

# A one-command runner: fork/exec, then wait4 for wall, cpu and peak RSS. Running
# each command in its own process keeps the figures independent.
cat > "$WORK/run1.py" <<'PY'
import os, sys, time
cmd = sys.argv[1:]
t0 = time.monotonic()
pid = os.fork()
if pid == 0:
    dn = os.open(os.devnull, os.O_WRONLY)
    os.dup2(dn, 1); os.dup2(dn, 2)
    try:
        os.execvp(cmd[0], cmd)
    except OSError:
        os._exit(127)
_, status, ru = os.wait4(pid, 0)
print("%d\t%.4f\t%.4f\t%d" % (os.waitstatus_to_exitcode(status),
      time.monotonic() - t0, ru.ru_utime + ru.ru_stime, ru.ru_maxrss))
PY

echo "host: $(uname -sm), rustc $(rustc --version | awk '{print $2}')"
echo
echo "=== compile time (cold build, cargo clean; release) ==="
printf '%-14s %3s %9s %9s %12s %12s %8s\n' crate ok wall_s cpu_s peakRSS_MB bin_bytes verif_syms
for c in no_verif build_verif runtime_verif; do
  d="$WORK/$c"
  ( cd "$d" && cargo clean >/dev/null 2>&1 )
  out=$(cd "$d" && python3 "$WORK/run1.py" cargo build --release)
  code=$(echo "$out" | cut -f1)
  wall=$(echo "$out" | cut -f2)
  cpu=$(echo "$out" | cut -f3)
  rssmb=$(awk -v k="$(echo "$out" | cut -f4)" 'BEGIN{printf "%.1f", k/1024}')
  bin=$(find "$d/target/release" -maxdepth 1 -name "bench_*" -type f -perm -u+x | head -n1 || true)
  size=0; syms="n/a"
  if [ -n "$bin" ]; then
    size=$(wc -c < "$bin" | tr -d ' ')
    if command -v nm >/dev/null 2>&1; then
      syms=$(nm -C "$bin" 2>/dev/null | grep -cE '(^|[^_A-Za-z0-9])verif::' || true)
    fi
  fi
  printf '%-14s %3s %9s %9s %12s %12s %8s\n' "$c" "$code" "$wall" "$cpu" "$rssmb" "$size" "$syms"
done

echo
echo "=== run time (7 runs each; median wall/cpu, peak RSS) ==="
printf '%-14s %10s %10s %12s\n' crate wall_s cpu_s peakRSS_MB
for c in no_verif build_verif runtime_verif; do
  bin=$(find "$WORK/$c/target/release" -maxdepth 1 -name "bench_*" -type f -perm -u+x | head -n1 || true)
  if [ -z "$bin" ]; then printf '%-14s  (no binary)\n' "$c"; continue; fi
  ws=""; cs=""; rs=""
  i=0
  while [ $i -lt 7 ]; do
    out=$(python3 "$WORK/run1.py" "$bin")
    ws="$ws $(echo "$out" | cut -f2)"
    cs="$cs $(echo "$out" | cut -f3)"
    rs="$rs $(echo "$out" | cut -f4)"
    i=$((i+1))
  done
  med_w=$(printf '%s\n' $ws | sort -n | sed -n '4p')
  med_c=$(printf '%s\n' $cs | sort -n | sed -n '4p')
  max_r=$(printf '%s\n' $rs | sort -n | sed -n '7p')
  rssmb=$(awk -v k="$max_r" 'BEGIN{printf "%.1f", k/1024}')
  printf '%-14s %10s %10s %12s\n' "$c" "$med_w" "$med_c" "$rssmb"
done

echo
echo "note: the build-time crate's build-dependency is compiled with cargo's"
echo "build-override profile (opt-level 0 by default), so its compile figures are"
echo "not directly comparable to the run-time crate's, whose dependency is compiled"
echo "at the release profile's opt-level. Set [profile.release.build-override]"
echo "opt-level = 3 to compare like with like -- the wall time then matches."
