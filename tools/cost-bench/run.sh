#!/bin/sh
# Print the cross-tool cost table the comparison README quotes.
#
# The comparison in `examples/comparison/` is about *correctness*: every tool in
# its table verifies the same three functions, and the point is what each one
# proves and what it catches. It has never been about cost, and the one cost
# figure it carried -- "`verif` decided all three functions in about 0.01 s; Kani
# and Prusti take seconds to minutes" -- was prose, not a measurement. This script
# is that measurement.
#
# It reports **three axes**, kept apart because folding them into one number is
# the usual way a comparison misleads:
#
#   setup        -- the one-time cost of installing the tool (disk).
#   verification -- the per-run cost of deciding the *same three functions*,
#                   wall / CPU / peak RSS, steady-state (see the note below).
#   artifact     -- what the tool adds to the binary you ship.
#
# The `artifact` axis is not measured here: only `verif` has an on-target shape
# (the others are all host-side binaries that ship nothing), and that axis is
# already measured by `tools/shape-bench/run.sh` -- `verif` build-time is 0
# symbols and the same bytes as the baseline; `verif` on-target is ~5.3 MB and 42
# symbols. Quoting it here would duplicate it and invite a false comparison: the
# other tools do not have the option to ship their prover, so "0 bytes" is not a
# win, it is a different shape.
#
# This is deliberately **not a gate**: the numbers move with the machine, and a
# CI job that asserted them would fail on a slower runner for a reason unrelated
# to the crate. `tools/comparison/run.sh` (gate 13) is the checked half -- it
# asserts the verdicts; this reports their cost. Exit 2 when no tool at all could
# be measured (nothing to report); 0 otherwise. A tool that is absent is named in
# the output, never silently dropped -- a table that shrank without saying so
# reads as "the tool was fast".
#
# The launcher is `tools/shape-bench/measurer.rs`, shared rather than copied: a
# second copy would be a second thing to drift, and the reasoning for reading
# `VmHWM` rather than `ru_maxrss` lives in one place (its header).
#
# Usage: sh tools/cost-bench/run.sh
#
# Environment: `VERIF_RUSTC` names the compiler the `verif` row uses (defaults to
# `rustc` on PATH); `VERUS_BIN` names the Verus driver and `VERUS_DIR` its install
# directory (both optional -- discovery falls back to PATH, then to the path this
# repo's setup notes install to). A tool that is not found is reported, not
# guessed at.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
cd "$ROOT"

if ! command -v cargo >/dev/null 2>&1; then
  echo "cost-bench: no cargo on PATH, so nothing was measured" >&2
  exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT INT TERM

MEASURER="$WORK/measurer"
rustc -O --edition 2024 -o "$MEASURER" "$ROOT/tools/shape-bench/measurer.rs"

FIXTURE="examples/comparison/target.rs"

# One measured run: median of three, so a single scheduler hiccup does not become
# the figure. The launcher prints `code  wall  cpu  peak_kb  sampled`.
#
# `-t` samples the whole descendant tree, not just the direct child. It matters
# for any tool that spawns a verifier or compiler: `cargo kani` is a thin cargo
# plugin whose real work is a `kani-driver` grandchild, and `verif`'s own driver
# spawns `rustc --emit=mir` to read the source. Without `-t` the launcher reports
# the launcher process's RSS (measured: kani 14 MB, verif 10 MB) instead of the
# real peak (kani 23 MB, verif 97 MB). Wall time is unaffected by the flag; only
# the peak is, which is the point. The largest single process's peak is reported,
# which is the right reading for a tree whose work is done by one heavy child.
measure() {
  label="$1"; shift
  best=""
  i=0
  while [ "$i" -lt 3 ]; do
    line="$("$MEASURER" -t "$@" 2>/dev/null || true)"
    code="$(printf '%s' "$line" | cut -f1)"
    if [ "${code:-1}" != "0" ]; then
      printf '%-14s %s\n' "$label" "FAILED (exit $code)"
      return
    fi
    wall="$(printf '%s' "$line" | cut -f2)"
    cpu="$(printf '%s' "$line" | cut -f3)"
    kb="$(printf '%s' "$line" | cut -f4)"
    best="${best}${wall} ${cpu} ${kb}\n"
    i=$((i + 1))
  done
  # median by wall time
  printf '%b' "$best" | sort -k1 -n | sed -n 2p | \
    awk -v l="$label" '{printf "%-14s %8.3f  %8.3f  %8.1f\n", l, $1, $2, $3/1024}'
}

printf '%-14s %8s  %8s  %8s\n' "tool" "wall_s" "cpu_s" "peak_MB"
printf '%-14s %8s  %8s  %8s\n' "----" "------" "-----" "-------"

# ---- verif: build the coverage driver once, then run it on the shared fixture.
# `mir_coverage` reads the source with `--emit=mir` and decides every function,
# which is the same three functions the other tools decide. It needs a compiler
# named; a stable `rustc` is enough (`--emit=mir` is stable).
#
# `--target-dir` is passed explicitly, to a private directory, rather than relying
# on the default `target/`. With `CARGO_TARGET_DIR` or a `build.target-dir` in
# Cargo config set, `cargo build` writes elsewhere while the launch path stayed
# `target/debug/...` -- so the harness either failed or, worse, silently measured
# a *stale* binary left in `target/` from an earlier build. An explicit
# `--target-dir` overrides both the env var and the config (verified), so the
# build and the launch cannot disagree, and the private dir also keeps this
# benchmark from clobbering the developer's own `target/`.
if command -v rustc >/dev/null 2>&1; then
  VERIF_RUSTC="${VERIF_RUSTC:-$(command -v rustc)}"
  export VERIF_RUSTC
  TARGET_DIR="$WORK/verif-target"
  if cargo build -q --features std --example mir_coverage --target-dir "$TARGET_DIR" >/dev/null 2>&1; then
    measure "verif" "$TARGET_DIR/debug/examples/mir_coverage" "$FIXTURE"
  else
    printf '%-14s %s\n' "verif" "SKIPPED (the example did not build)"
  fi
else
  printf '%-14s %s\n' "verif" "SKIPPED (no rustc)"
fi

# ---- Kani: needs its own crate with a `#[cfg(kani)]` harness, because a Kani
# proof is a Rust function. The fixture is the committed `kani.rs`, copied in
# verbatim so the two sides prove the same statements.
if command -v cargo >/dev/null 2>&1 && cargo kani --version >/dev/null 2>&1; then
  K="$WORK/kani"
  mkdir -p "$K/src"
  cp examples/comparison/kani.rs "$K/src/lib.rs"
  cat > "$K/Cargo.toml" <<'EOF'
[package]
name = "cost_bench_kani"
version = "0.1.0"
edition = "2021"

[dependencies]
kani-verifier = { version = "0.68.0", optional = true }

[features]
kani = ["dep:kani-verifier"]
EOF
  ( cd "$K" && cargo kani --features kani >/dev/null 2>&1 ) || true   # warm the harness build
  ( cd "$K" && measure "kani" "cargo" "kani" "--features" "kani" )
else
  printf '%-14s %s\n' "kani" "SKIPPED (cargo-kani not installed)"
fi

# ---- Verus: one self-contained `.rs`, run through the `verus` driver. The
# driver needs the rust toolchain its release pins; if that is missing, `verus`
# exits non-zero and the run is reported FAILED rather than dropped.
#
# `VERUS_BIN` is *defined* before the loop -- as `${VERUS_BIN:-}`, which keeps an
# inherited value -- rather than assigned `""`. An empty assignment wipes the path
# the loop's first candidate reads, and leaving it entirely unset makes the
# `[ -n "$VERUS_BIN" ]` below abort the whole run under `set -u` whenever no Verus
# is installed, taking the Coq, Lean and setup measurements with it. Discovery
# order: an inherited `VERUS_BIN`, then `$VERUS_DIR/verus`, then PATH, then the
# location this repo's setup notes install to.
VERUS_BIN="${VERUS_BIN:-}"
for c in "$VERUS_BIN" "${VERUS_DIR:-}/verus" "$(command -v verus 2>/dev/null || true)" /tmp/verus/verus-x86-linux/verus; do
  if [ -n "$c" ] && [ -x "$c" ]; then VERUS_BIN="$c"; break; fi
done
if [ -n "$VERUS_BIN" ]; then
  cp examples/comparison/verus.rs "$WORK/verus_example.rs"
  # Warm the driver's own cache once, as for kani, so all three measured runs are
  # steady-state and the reported median is not a blend of a cold and a warm run.
  ( cd "$ROOT" && "$VERUS_BIN" --crate-type=lib "$WORK/verus_example.rs" >/dev/null 2>&1 ) || true
  measure "verus" "$VERUS_BIN" "--crate-type=lib" "$WORK/verus_example.rs"
else
  printf '%-14s %s\n' "verus" "SKIPPED (verus not found; set VERUS_BIN or VERUS_DIR)"
fi

# ---- Coq: two files. The model is compiled once (it is the hand-written model
# the proof is *about*), then the example is the measured unit. Reported figure
# is the example alone; the model's cost is named in the note below.
if command -v coqc >/dev/null 2>&1; then
  ( cd "$ROOT" && coqc -Q examples/comparison/coq "" examples/comparison/coq/model.v >/dev/null 2>&1 ) || true
  measure "coq" "coqc" "-Q" "examples/comparison/coq" "" "examples/comparison/coq/example.v"
  rm -f examples/comparison/coq/*.vo examples/comparison/coq/*.glob examples/comparison/coq/.*.aux 2>/dev/null || true
else
  printf '%-14s %s\n' "coq" "SKIPPED (coqc not installed)"
fi

# ---- Lean: model compiled to an `.olean`, then the example measured against it.
if command -v lean >/dev/null 2>&1; then
  ( cd "$ROOT" && lean -o "$WORK/model.olean" examples/comparison/lean/model.lean >/dev/null 2>&1 ) || true
  LEAN_PATH="$WORK" measure "lean" "lean" "examples/comparison/lean/example.lean"
else
  printf '%-14s %s\n' "lean" "SKIPPED (lean not installed)"
fi

echo
echo "=== setup: one-time install cost (measured on disk; install-method dependent) ==="
# `du` on whatever the tool installed, so the figure is what is actually there
# rather than a download-size claim. A tool that installs nothing of its own
# (verif -- a crate) reports the crate download.
setup() {
  label="$1"; shift
  total=0
  for d in "$@"; do
    if [ -e "$d" ]; then
      kb="$(du -sk "$d" 2>/dev/null | cut -f1)"
      total=$((total + kb))
    fi
  done
  if [ "$total" -eq 0 ]; then
    printf '%-14s %s\n' "$label" "not found on this machine"
  else
    awk -v l="$label" -v k="$total" 'BEGIN{printf "%-14s %8.1f MB\n", l, k/1024}'
  fi
}
# verif is a crate, not an installed tool: its "setup" is the crate download.
if command -v python3 >/dev/null 2>&1; then
  size="$(curl -s -A "cost-bench" "https://crates.io/api/v1/crates/verif/0.1.0" 2>/dev/null \
    | python3 -c "import sys,json; print(json.load(sys.stdin)['version']['crate_size'])" 2>/dev/null || true)"
  if [ -n "${size:-}" ]; then
    awk -v k="$size" 'BEGIN{printf "%-14s %8.1f MB (the crate, from crates.io)\n", "verif", k/1048576}'
  else
    printf '%-14s %s\n' "verif" "crate size unavailable (offline)"
  fi
else
  printf '%-14s %s\n' "verif" "crate size unavailable (no python3)"
fi
setup "kani" "$HOME/.kani" "$HOME/.cargo/bin/cargo-kani" "$HOME/.cargo/bin/kani"
# The setup row measures the *directory* Verus installed into -- not the directory
# that happens to hold a `verus` entry. Two ways those differ. An explicit
# `VERUS_DIR` names the installation and must win over discovery. And a `VERUS_BIN`
# that is a symlink -- the common `/usr/local/bin/verus -> /opt/verus/verus` layout
# -- makes `dirname` name the *link's* directory, so the figure would be a shared
# bin dir (a few kB) and none of the distribution (hundreds of MB). So: honour
# `VERUS_DIR` first; otherwise resolve the driver through its symlinks
# (`readlink -f`), take the real directory, and accept it only when it carries
# `rust_verify`, the marker of a Verus distribution. When discovery found no driver
# at all -- it already tried the documented install path -- the honest row is "not
# found", not a size for a directory that holds no Verus.
if [ -n "${VERUS_DIR:-}" ]; then
  setup "verus" "$VERUS_DIR"
elif [ -n "${VERUS_BIN:-}" ]; then
  verus_real="$(readlink -f "$VERUS_BIN" 2>/dev/null || printf '%s' "$VERUS_BIN")"
  verus_home="$(dirname "$verus_real")"
  [ -e "$verus_home/rust_verify" ] || verus_home=""
  setup "verus" "$verus_home"
else
  setup "verus"
fi
# Coq installs spread across `/usr` and `~/.opam`; `dpkg` reports its own size
# where the distribution package was used, which is the honest figure for that
# install method. A source/opam build would be measured with `du` instead.
if command -v dpkg-query >/dev/null 2>&1; then
  kb="$(dpkg-query -W -f='${Installed-Size}\n' coq libcoq-core-ocaml libcoq-stdlib 2>/dev/null | awk '{s+=$1} END{print s+0}')"
  if [ "${kb:-0}" -gt 0 ]; then
    awk -v k="$kb" 'BEGIN{printf "%-14s %8.1f MB (distribution packages)\n", "coq", k/1024}'
  else
    setup "coq" "/usr/lib/ocaml/coq" "/usr/share/coq"
  fi
else
  setup "coq" "/usr/lib/ocaml/coq" "/usr/share/coq"
fi
setup "lean" "$HOME/.elan"

cat <<'EOF'

notes:
  - One machine, x86_64, four cores. Regenerate rather than trusting the prose.
  - These are **steady-state** figures, not cold-cache: kani and verus warm their
    own caches on the first run, so the harness runs each tool once to warm it and
    then reports the median of three warm runs. The gap is large -- kani is ~3.2 s
    / ~256 MB cold and ~0.7 s / ~23 MB warm on this machine -- so a "cold" label
    here would be wrong by 4x. What the number answers is "what does a repeated
    check cost", which is the interesting one; a one-shot first run is a different
    (and much larger) figure.
  - Peak RSS samples the whole process tree (`-t`), so it includes the verifier or
    compiler a tool spawns. That is why verif's row is ~97 MB rather than ~10 MB:
    its driver spawns `rustc --emit=mir`, and the largest process in the tree is
    the peak. Sampling only the direct child would report the launcher's RSS.
  - verif's figure includes spawning `rustc --emit=mir` to read the source; the
    engine-only cost of the same three functions is lower (see the comparison
    README, which separates the two). It is the only row whose "verification"
    step also compiles the code it verifies.
  - coq and lean prove a *hand-written model* of the three functions, not the
    Rust code; the model is compiled once and its cost is not in the row above.
    That transcription is the risk the comparison README is about, and it is why
    their rows are not "the same thing, slower".
  - Prusti and SPARK are in the comparison README's correctness table but not
    here: Prusti needs a pinned nightly and a JDK, and gnatprove pulls four
    solvers. Add them the same way if you need their cost.
EOF
