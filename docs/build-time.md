# Build-time verification

Part of the [`verif` README](../README.md).

## Two ways to use the verifier: at build time, or on the target

The claim above — the prover is *in* the artifact — is one of **two shapes** this crate can
take, and the choice is real. The first is what Kani and Verus do and what a
size-constrained safety build usually wants; the second is the crate's own headline.

Both are reachable from the same dependency. What changes is *where* the obligation is
discharged and *what* the shipped artifact carries.

### Shape A — verify at build time (the Kani/Verus shape)

Put `verif` in `[build-dependencies]`, call the frontend from `build.rs`, and fail the
build when an outcome is not `Verified`. The `mir` frontend is already `std`-only host
tooling, so there is nothing else to wire up:

```rust,ignore
// build.rs
fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    let report = verif::mir::verify::verify_file_with("rustc", "src/lib.rs".as_ref(), &[])
        .expect("the MIR frontend could not read the source");
    for (name, outcome) in &report.outcomes {
        println!("cargo:warning=verif {name}: {outcome}");
        assert!(outcome.is_verified(), "verif: {name} is not verified: {outcome}");
    }
}
```

That is the whole recipe when the contracts are `///` doc comments. A source file that
wants to *name* `verif` — an in-code contract block, `use verif::spec;` — needs one more
step, because the frontend runs `rustc` on a single file with no Cargo graph behind it, so
without an `--extern` entry the import is `E0432: unresolved import`. `extern_options`
supplies it, and the crate must then also be an ordinary dependency (the macro is real
code the crate's own compilation needs):

```toml
[dependencies]
verif = { version = "0.2", features = ["std"] }

[build-dependencies]
verif = { version = "0.2", features = ["std"] }
```

```rust,ignore
// build.rs — the extern-aware form
fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    // One compiler for both steps. `extern_options_with` returns the rlib *this*
    // compiler accepts, so passing the same name to the emitter cannot disagree.
    // Cargo sets `RUSTC` for a build script to the compiler that produced the
    // build-dependency rlibs, which is the one that can read them back.
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let opts = verif::mir::verify::extern_options_with(&rustc, "verif").unwrap_or_default();
    let report = verif::mir::verify::verify_file_with_opts(
        &rustc, "src/lib.rs".as_ref(), &[], &opts,
    )
    .expect("the MIR frontend could not read the source");
    // A report with no outcomes verified nothing, and a loop over an empty list
    // would pass silently. Demand at least one obligation was discharged.
    assert!(
        !report.outcomes.is_empty(),
        "verif: no contract was found in src/lib.rs, so nothing was verified"
    );
    for (name, outcome) in &report.outcomes {
        assert!(outcome.is_verified(), "verif: {name} is not verified: {outcome}");
    }
}
```

**The lookup and the MIR emission must name the same compiler.** An rlib's metadata is
compiler-specific: a candidate the *producing* compiler accepts is not thereby readable by
a *different* one, so probing with one toolchain and emitting with another fails `E0514`
even when both are installed and each has its own artifact. That is why the recipe above
resolves one `rustc` and passes it to both calls. The convenience form `extern_options`
(no compiler argument) reads `VERIF_RUSTC`, which is what the emitter uses, so it is
consistent only when `VERIF_RUSTC` is also the compiler that built the rlib — true for the
common `cargo build` with no override, and the reason the explicit form exists for every
other case. Because that reasoning is easy to get wrong, it is also *checked*:
`extern_options_with` records the compiler it probed with in `MirOptions::probed_with`,
and `verify_file_with_opts` refuses to emit with a different one, naming both and the fix
rather than leaving a `E0514`/`E0432` about a program that is fine. Hand-built
`MirOptions` (where the caller names a prebuilt rlib) are not checked, since only the
caller knows which compiler built it.

`extern_options` does not guess: a crate that is both a dependency and a build dependency
has *two* rlibs of one name, and a stale one from another compiler is `E0514`. So each
candidate is handed to `rustc` on a one-line probe and the first that compiles is returned;
`None` means nothing compiled, and `unwrap_or_default()` then yields the plain recipe
above, which is a *skipped* extern rather than a wrong one. The zero-cost property is
unchanged — the macro expands to nothing, so the artifact carries no prover symbol either
way (gate 18 measures this).

A build script is a *separate compilation unit*: cargo compiles it for the host, runs it,
and throws it away. So the decision procedure — the whole BDD blasting and CDCL fallback —
is never linked into the crate's own artifact. That is not an optimisation, it is a
consequence of the build model, and it is what makes the two properties below both true at
once:

* **The verification happens at compile time.** A false contract is a build error naming
  the broken obligation and its witness, exactly as it is under Kani or Verus. Nothing is
  checked at runtime, so nothing can be skipped in a release build. (There is no separate
  "build-time vs compile-time" mode: verifying from `build.rs` *is* verifying at compile
  time. The real second mode is the one below.)
* **The artifact is zero-cost.** With `verif` as a build dependency the crate's own binary
  carries **zero** `verif` symbols — see the measured table below.

This is gate 18 of `scripts/gate.sh`, run by `tools/build-verify/run.sh` on a scratch crate
it creates and removes. It is a gate rather than a paragraph because "zero cost" and
"verified at compile time" are both checkable claims, and both rot silently if only
asserted: the script requires a good contract to build *and* the verifier to report
`verified` (a build script that silently did nothing would otherwise pass), a broken
contract to fail the build on its named obligation, and the resulting rlib to carry no
prover symbols. It runs those checks for **both spellings** -- a `///` contract and an
in-code `spec! { … }` block -- because the in-code path is a different compilation (the
source names `verif` in a `use`), and a macro that expands to nothing is a claim about that
artifact, not the doc-comment one. The in-code half also requires a *false* contract to fail
the build: a scanner that read `requires:` and silently dropped `ensures:` would otherwise
pass the true-contract check while proving nothing.

### Shape B — verify on the target (the prover in the artifact)

Add `verif` as an ordinary dependency and call the engine from your own code. Now the
decision procedure *is* in the binary and the obligation is discharged **at run time**, on
the machine that runs the program — which is the point: a proof that can run where Z3
cannot. `examples/bare_metal.rs` is the extreme case: `#![no_std]`, no `main`, the
decision procedure compiled for `thumbv7em-none-eabihf` and built by Ferrocene.

The `smt` engine needs no `std` and no allocator (the default build is `no_std`), so this
shape works on an MCU. It is **not** zero-cost: you ship the engine, and you pay for it in
binary size and in the time the proofs take when they run.

### The same function, two ways

One function, one contract; the difference is only *when* the obligation is discharged.
The contract is written once, in a `spec!` block in the same file, and read by the MIR
frontend:

```rust
// The function under verification, with its contract fused into the file. The
// `spec!` block expands to nothing, so this compiles as ordinary Rust too.
use verif::spec;

spec! {
    requires: n <= 1_000_000,
    ensures: ret <= 100,
}
pub fn clamp100(n: u32) -> u32 {
    if n > 100 { 100 } else { n }
}
```

The contract is read from the *source text*, not from an attribute, for the reason the
[contracts](mir.md#contracts-one-spelling-in-the-code-it-describes) section gives: rustc's MIR
dump carries no attributes, so the frontend reads the contract from the source and the
body from MIR.

**Verified at build time** — nothing about the function changes; the proof lives in
`build.rs` and runs while the crate is compiled. A false contract stops the build, and the
shipped binary contains none of the prover:

```rust,ignore
// build.rs — the verifier, as a build script
use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=src/lib.rs");
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());
    // The frontend runs `rustc` on one file with no Cargo graph behind it, so the
    // source's own `use verif::spec;` needs an `--extern` entry. This locates the
    // rlib the build script is already linked against, and the search paths its
    // dependencies live on, so `verif` and `verif-arithmetic` both resolve.
    let opts = verif::mir::verify::extern_options_with(&rustc, "verif").unwrap_or_default();
    let report = verif::mir::verify::verify_file_with_opts(
        &rustc,
        Path::new("src/lib.rs"),
        &[],
        &opts,
    )
    .expect("the MIR frontend could not read the source");
    // A report with no outcomes is a build that verified nothing, and a loop over
    // an empty list would pass silently -- the "harness that cannot fail" this
    // repository treats as a defect. Demand at least one obligation was discharged.
    assert!(
        !report.outcomes.is_empty(),
        "verif: no contract was found in src/lib.rs, so nothing was verified"
    );
    for (name, outcome) in &report.outcomes {
        assert!(outcome.is_verified(), "verif: {name} is not verified: {outcome}");
    }
}
```

`extern_options` is the `VERIF_RUSTC`-aware form of the same call; use
`extern_options_with` when the script resolves its own compiler, so the lookup and the
emission name one toolchain (an rlib's metadata is compiler-specific, and probing with one
compiler then emitting with another is an `E0514` against a program that is fine).

**Verified on the target** — the same bound is discharged by the engine compiled into the
binary, at the moment the function runs. The engine is `no_std`, so this compiles for bare
metal; it is the shape `examples/bare_metal.rs` demonstrates:

```rust
use verif::prelude::*;

/// The same function, with the same bound, checked at run time instead of at build time.
pub fn clamp100(n: u32) -> u32 {
    let ok = verif::smt::with_fresh(|| {
        let x = var(32);
        // the clamped result is always <= 100, for every x
        let clamped = verif::smt::ite(x.gt_val(100), verif::smt::word(100, 32), x);
        clamped.le_val(100).prove().is_proved()
    });
    assert!(ok, "clamp100's bound did not discharge");
    if n > 100 { 100 } else { n }
}
```

The two are not interchangeable. The build-time shape proves the contract *of the code you
shipped*, once, and costs nothing at run time; the on-target shape can prove a property of
*values the program has right now*, on hardware where no solver process can run, and pays
for the engine. A flight build might use the first to keep the artifact small and the
second for an on-target re-check of a critical invariant.

### What each shape costs

Four crates share one business function and one driver — the `clamp100` above, exercised
in a loop — so the only difference between the rows is how verification is attached.
`no_verif` is the baseline, `build_verif` puts `verif` in `[build-dependencies]`,
`runtime_verif` calls the engine from `main` and discharges the `clamp100` bound at run
time, and `unused_verif` links the engine but never calls it. Measured on `x86_64`,
`release`, rustc 1.100, four cores; regenerate with `sh tools/shape-bench/run.sh`:

| | no verif | verif (build) | verif (runtime) | verif (unused) |
|---|---|---|---|---|
| **compile** wall time | 0.16 s | 3.4 s | 12.9 s | 12.7 s |
| **compile** CPU time | 0.17 s | 5.1 s | 34.9 s | 35.1 s |
| **compile** peak RSS (build tree) | 96 MB | 433 MB | 502 MB | 508 MB |
| **binary size** | 438 312 B | 438 328 B | 5 775 256 B | 438 336 B |
| **run** wall time (median of 7) | 3.1 ms | 3.2 ms | 4.6 ms | 3.2 ms |
| **run** CPU time | 3.0 ms | 3.0 ms | 4.5 ms | 2.9 ms |
| **run** peak RSS | 2.1 MB | 2.1 MB | 5.6 MB | 2.1 MB |
| `verif` symbols in the binary | 0 | **0** | 42 | 0 |
| where verification happens | — | compile time | run time | nowhere |

Reading the table honestly:

* **Build-time verification is zero-cost in the artifact, not in the build.** The binary
  is the baseline to within 16 bytes (438 312 → 438 328 B; the residue is the crate name in
  the embedded metadata — `bench_build_verif` is longer than `bench_no_verif`, so the two
  are not byte-identical, but the prover leaves no code) and carries zero `verif` symbols,
  and the run-time figures are identical. The price is paid at compile time: a host-side
  `rustc` runs the MIR frontend and the decision procedure, so the cold build goes from
  0.16 s to 3.4 s and the build tree's peak RSS rises to ~433 MB (that peak is one `rustc`
  compiling the `verif` crate, not the prover's own arena).
* **On-target verification costs size and a little run time.** The engine adds ~5.3 MB
  (≈13×) to the binary and ~1.5 ms to the run. The ~1.5 ms is one obligation being
  discharged by the embedded engine — the real `clamp100` bound
  `ite(x > 100, 100, x) <= 100` at 32 bits, not a tautology. Measured in-process over
  1000 repetitions, the engine's per-proof cost for that obligation is **~290 µs**; a wide
  multiplier past the BDD wall is `Unknown` rather than slow, as the scaling notes
  elsewhere say. (An earlier version of this table quoted ~14 µs, but that proof was
  `x < 65536 || x >= 65536` on a 16-bit variable — a predicate that folds to `true` before
  the solver sees it, so it measured the harness, not the engine.)
* **A dependency you never call is also zero-cost** — dead-code elimination leaves a
  438 336-byte binary with zero `verif` symbols. But that is the linker dropping an unused
  library, not a proof: nothing was verified.
* **The compile figures are not a like-for-like profile comparison.** Cargo compiles
  build-dependencies with the `build-override` profile, which defaults to `opt-level = 0`,
  while a normal dependency is compiled at the release profile's `opt-level = 3`. So the
  3.4 s row is "what a user gets by default", not "build-dependencies are inherently
  cheaper": set `[profile.release.build-override] opt-level = 3` and the build-time row's
  wall time rises to ≈12.9 s, matching the run-time row. The engine is the same work
  either way; only its optimisation level differs.

The RSS figures are read from `/proc/<pid>/status:VmHWM` by
`tools/shape-bench/measurer.rs`, the native launcher this table's numbers come from. A
`fork`-based harness (Python's `os.wait4`) reports `ru_maxrss`, which is the child's
resident high-water mark *since the fork* — so the launcher's own RSS becomes a floor
under every measurement. That floor is invisible on a build (a `rustc` peaks at ~500 MB)
and dominant on a run (a benchmark binary peaks at ~2 MB): the same `no_verif` run
reports 2.1 MB through the native launcher and 5.5 MB through a Python fork, because
5.5 MB is Python's own RSS. The launcher's header records the full reasoning.

The numbers are a measurement, not a guarantee; `tools/shape-bench/run.sh` prints them on
your machine. The *properties* — verification at build time, and no prover in the
artifact — are what gate 18 asserts, because a cost figure moves with the machine and a
property does not.

### When each shape is actually worth using

The two shapes are not equals, and the honest reading is that **one is the default and the
other is a narrow special case**. Saying so is more useful than presenting them as a
symmetric choice.

**Build time is the right default, for almost everyone.** Reach for it when:

- the claim is a property of the *code for all inputs* (`∀ n. clamp100(n) <= 100`) — that
  is what a contract states, and it is a statement about the program, not about one run;
- you build on a normal host (a `rustc` that can `--emit=mir`, and `std`), and
- the artifact should stay small: the shipped binary carries zero `verif` symbols, and the
  build-time row above is the same bytes as the baseline.

Its cost is a slower build (≈3.4 s here) and a host toolchain. Its limit is coverage: the
frontend models a subset of Rust, so a function that reaches an unmodelled shape comes back
`Incomplete` — which is *not* a proof, and must not be read as one.

**On the target is for a narrow case, and it is easy to reach for it wrongly.** The
on-target shape is worth its cost only when **all** of these hold:

- the property is a relation between *values the program has right now*, unknown at
  compile time (a calibration constant, a sensor reading, a runtime config), **and**
- the property is non-trivial — several variables, or bit-vector structure that is awkward
  to write as a direct check, **and**
- there is no solver that can be run there (bare metal, offline), **and**
- the check is *rare* — boot-time or config-time, not per control-loop iteration.

If any of those is missing, the engine is the wrong tool. The section's own example makes
the point: proving `ite(x>100,100,x) <= 100` costs ≈290 µs (measured, `shape-bench`),
while the *same* check as `assert!(n <= 100)` is one comparison — nanoseconds. For a single
concrete value, `assert!` or `checked_add` is always cheaper and clearer, and it needs no
engine. The on-target shape earns its ≈5.3 MB and its hundreds of microseconds only when
the property is genuinely *symbolic* at that point and cannot be checked by evaluating it.

So the practical rule is: **default to build time; reach for on-target only with an
explicit answer to "which dynamic property, why is it not a plain `assert`, and why can it
not be checked at build time".** If those three do not have answers, use `assert!`.

What the crate is *actually* unusual at is not "the prover can run on the target" — that is
an impressive demo and a narrow use — but that the prover is **a zero-dependency, `no_std`,
allocator-free library you can embed**. That is what makes it usable inside your own tooling
without pulling in Z3 or a solver process, and it is the property to weigh against the
mature, higher-coverage competitors.

### How the cost compares to other verifiers

The comparison in [`examples/comparison/`](../examples/comparison/README.md) is about
*correctness* — every tool there verifies the same three functions, and the finding is what
each proves and what it catches. It is **not** a cost comparison, and the one cost sentence
it used to carry ("`verif` decided all three functions in about 0.01 s; Kani and Prusti take
seconds to minutes") was prose, not a measurement. `tools/cost-bench/run.sh` is the
measurement; run it and compare rather than trusting any figure here.

Cost has **three axes**, and folding them into one number is the usual way a comparison
misleads:

| axis | what it is | where the numbers are |
| --- | --- | --- |
| **setup** | one-time install | below, and `tools/cost-bench/run.sh` |
| **per verification** | deciding the same three functions | below, and `tools/cost-bench/run.sh` |
| **artifact** | what the tool adds to the binary you ship | `tools/shape-bench/run.sh` |

Measured on one machine (x86_64, four cores; Kani 0.68.0, Verus 0.2026.11.02, Coq 8.20.1,
Lean 4.36.0, rustc 1.100.0), steady-state (each tool warmed once, then the median of three
runs — Kani is ≈3.2 s / ≈256 MB on a *cold* first run), the same three functions:

| tool | per-verification wall | peak RSS | setup (on disk) |
| --- | --- | --- | --- |
| `verif` | ≈0.07 s | ≈97 MB | ≈1.4 MB (a crate) |
| Kani | ≈0.7 s | ≈23 MB | ≈486 MB |
| Verus | ≈0.8 s | ≈316 MB | ≈133 MB |
| Coq | ≈0.5 s | ≈298 MB | ≈451 MB |
| Lean | ≈0.5 s | ≈472 MB | ≈3.1 GB |

Read the table with these caveats, each of which is the honest part:

- **`verif`'s row includes spawning `rustc --emit=mir`** to read the source — it is the
  only row whose verification step also compiles the code it verifies. That is also why its
  peak RSS is ≈97 MB, not the ≈10 MB the driver process alone peaks at: the *largest process
  in the tree* is the peak, and for `verif` that is the `rustc` it spawns. The engine-only
  cost of the same three functions is ≈0.05 s (the per-function `elapsed` column
  `mir_coverage` prints), so "≈0.07 s" is not "the engine is 10× faster than Kani" — it is a
  measurement that includes the frontend's compiler call. Peak RSS is a **tree** figure for
  every row, so each number is the tool's real peak and not its launcher's.
- **Coq and Lean prove a hand-written *model*, not the Rust code.** Their rows are not "the
  same thing, slower" — they are a different task, and the transcription is the risk the
  comparison README is about. A like-for-like engine comparison would exclude them.
- **Prusti and SPARK are missing** because their installs are heavy (a pinned nightly and a
  JDK; four bundled solvers). Their absence is named, not hidden — a table that shrank
  silently reads as "the tool was fast".
- **The artifact axis is where `verif` on-target *loses*, and the others have no entry.**
  Kani, Verus, Coq and Lean are host-side binaries that ship nothing; `verif` build-time
  also ships nothing. `verif` on-target ships ≈5.3 MB and 42 symbols. That is the deliberate
  trade for running where no solver can, and it is why the two shapes are not interchangeable.
- **These are steady-state figures, not a cold first run.** Kani and Verus warm their own
  caches on the first run, so the harness warms each once and reports the median of three
  warm runs. The gap is large — Kani is ≈3.2 s / ≈256 MB cold against ≈0.7 s / ≈23 MB warm —
  so a "cold cache" label would be wrong by 4×. The number answers "what does a repeated
  check cost", which is the useful one; a one-shot first run is larger.
- **These are one machine's figures.** They move with CPU, disk and cache. `verif` wins the
  setup axis clearly and is competitive on the per-verification axis for this small fixture;
  it does **not** claim to win on speed for large problems — the BDD scaling wall is real and
  documented above, and the mature competitors have higher coverage (pointers, aliasing,
  concurrency, unbounded induction). The reason to choose `verif` is *embeddability and no
  external toolchain*, not raw speed.

### Shape C — verify as part of `cargo build` (`verif-wrap`)

`verif-wrap` is a `RUSTC_WRAPPER`: `RUSTC_WRAPPER=/path/to/verif-wrap cargo build`
forwards every `rustc` call through it, verifies the *primary* package's contracts, and
fails the build on a false one. It forwards `--cfg`/`--target` to its MIR emit (so a
feature-flipped `cfg!` is the program the build compiles) and **refuses** a cross target
whose pointer width or endianness the model does not represent (64-bit `usize`, the
verifier's own byte order) rather than pass a proof about a different layout.

Two limits are documented, not hidden: it verifies the primary package only (a
dependency's contracts are not checked), and Cargo calls a wrapper only when it compiles —
so after an unwrapped build, enabling the wrapper can reuse a cached, unchecked artifact.
Build verified and unchecked artifacts in **separate target directories** (e.g.
`CARGO_TARGET_DIR=target/verif`) so a cached build cannot bypass the check.
