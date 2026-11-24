//! The MIR frontend's coverage scoreboard: how much *realistic* Rust does it decide?
//!
//! This is deliberately **not** a gate. `scripts/gate.sh` asserts verdicts on
//! `examples/mir_targets/actuator.rs`, a regression corpus where every function
//! is expected to be decided. This example measures the opposite: it runs the
//! frontend over `examples/mir_targets/realistic.rs`, a corpus of ordinary Rust
//! that is *not* curated to be decidable, and prints the tally. A roadmap that
//! says "widen real-Rust support" is unfalsifiable; a number that moves from 2 to
//! 12 is not. So the scoreboard is the roadmap's evidence, and it exits 0
//! whatever it finds. The remainder it does not decide are the *next* gaps, and
//! each one names itself in the `detail` column rather than being summarised.
//!
//! Run it with a compiler named, or it falls back to `rustc` on `PATH`:
//!
//! ```console
//! $ VERIF_RUSTC="$(rustup which rustc)" \
//!     cargo run --features std --example mir_coverage
//! function             outcome      detail
//! halve_guarded        verified     2 obl, 1 panic
//! pick_from            skipped      unreadable `requires`: unknown name `c` ...
//! sum_to               verified     5 obl, 2 panic
//! is_nonzero_after     verified     3 obl, 0 panic
//! ...
//! decided 10 of 14
//! ```
//!
//! An unrecognised argument is treated as a path, so a new corpus can be
//! measured without editing this file. A second argument names one function to
//! measure on its own, which is what makes a slow shape attributable: the
//! engine has a size budget, not a time budget, so a shape can take a long time
//! without ever answering `Unknown`. A single named target is timed on its own, so
//! its elapsed time is the evidence for where that time goes; a full run reports
//! one batch time and a numerator and denominator drawn from the same inventory.

use std::path::PathBuf;
use std::time::Instant;

use verif::mir::spec;
use verif::mir::verify::{self, FnOutcome};

const DEFAULT_TARGET: &str = "examples/mir_targets/realistic.rs";

fn main() {
    let mut args = std::env::args().skip(1);
    let target = args.next().unwrap_or_else(|| DEFAULT_TARGET.into());
    let only: Option<String> = args.next();
    let src = PathBuf::from(&target);
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());

    let (mir, edition) = match verify::emit_mir_with_opts(&rustc, &src, &verify::MirOptions::default())
    {
        Ok(m) => m,
        Err(e) => {
            // "the tool could not run" must never look like "the code is wrong",
            // so this is a distinct message and a distinct exit. The error already
            // names the compiler, the edition that was used and the reason (a
            // missing edition, a compiler error), so it is printed as it stands
            // rather than followed by a hint that would send the reader after the
            // wrong toolchain -- `--emit=mir` is stable, and an edition error is
            // not a toolchain problem.
            eprintln!("mir_coverage: could not get MIR from {}: {e}", src.display());
            std::process::exit(2);
        }
    };

    let source = match std::fs::read_to_string(&src) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("mir_coverage: cannot read {}: {e}", src.display());
            std::process::exit(2);
        }
    };
    // File-aware: the driver compiles the whole crate, so the specs must carry each
    // module's file too, or a cfg-disabled root method could pair with a module body at
    // the same coordinates. `extract_crate` gives `original_loc` a file for every impl.
    let specs = spec::extract_crate(&src, &source);

    println!("# {target} ({edition})");
    if only.is_none() {
        println!("{:<22} {:<12}  detail", "function", "outcome");
    } else {
        println!("{:<22} {:<12} {:>9}  detail", "function", "outcome", "elapsed");
    }
    let mut decided = 0usize;
    // The single-function branch filters by the requested name. The full run passes
    // an EMPTY filter so the driver selects every resolved target -- including impls
    // that only *inherit* a trait contract and so carry no direct contract to list.
    // A name-based filter would silently skip those, leaving them unchecked.
    let mut total = 0usize;
    match &only {
        // One named target: its own call, so the row's elapsed time is that function's
        // -- the attribution path for a slow shape.
        Some(want) => {
            let started = Instant::now();
            match verify::verify_mir_text(&mir, &specs, std::slice::from_ref(want)) {
                Ok(report) => {
                    let elapsed = started.elapsed();
                    total = report.outcomes.len() + report.missing.len();
                    for (fname, outcome) in &report.outcomes {
                        let (label, detail) = describe(outcome);
                        if label == "verified" {
                            decided += 1;
                        }
                        let short: String = detail.chars().take(72).collect();
                        println!("{fname:<22} {label:<12} {:>8.2}s  {short}", elapsed.as_secs_f64());
                    }
                    for m in &report.missing {
                        println!("{:<22} {:<12}  {m}", "missing", "unchecked");
                    }
                }
                Err(e) => println!("{want:<22} {:<12} driver error: {e}", "error"),
            }
        }
        // Full corpus: one pass so a definition selected by two names is counted once,
        // and the numerator and denominator come from the SAME inventory (the report),
        // so an inherited-only corpus cannot print `decided N of 0`.
        None => {
            let started = Instant::now();
            match verify::verify_mir_text(&mir, &specs, &[]) {
                Ok(report) => {
                    // Read the clock before printing so `elapsed` is engine-only, not the
                    // cost of formatting every row.
                    let elapsed = started.elapsed();
                    // The whole inventory: checked outcomes plus contracts the driver could
                    // not pair with a body, so a dropped contract cannot look covered.
                    total = report.outcomes.len() + report.missing.len();
                    for (fname, outcome) in &report.outcomes {
                        let (label, detail) = describe(outcome);
                        if label == "verified" {
                            decided += 1;
                        }
                        // Truncate on a char boundary, not a byte offset: a counterexample
                        // can contain a multi-byte character and slicing blind would panic.
                        let short: String = detail.chars().take(72).collect();
                        println!("{fname:<22} {label:<12}  {short}");
                    }
                    // An unmatched contract is in the denominator; name it so the reader
                    // can see which contract went unchecked rather than a bare total.
                    for m in &report.missing {
                        println!("{:<22} {:<12}  {m}", "missing", "unchecked");
                    }
                    println!("\nelapsed {:.2}s", elapsed.as_secs_f64());
                }
                Err(e) => println!("error        driver error: {e}"),
            }
        }
    }
    if only.is_none() {
        println!("\ndecided {decided} of {total}");
    }
}

/// The label and detail for one outcome, so the `match` lives in one place.
fn describe(outcome: &FnOutcome) -> (&'static str, String) {
    match outcome {
        FnOutcome::Verified { obligations, panics_ruled_out } => (
            "verified",
            format!("{obligations} obligation(s), {panics_ruled_out} panic(s) ruled out"),
        ),
        FnOutcome::Failed { kind, detail } => ("FAILED", format!("{kind} — {detail}")),
        FnOutcome::Incomplete { reasons, .. } => ("incomplete", reasons.join("; ")),
        FnOutcome::Skipped { reason } => ("skipped", reason.clone()),
    }
}
