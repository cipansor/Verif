//! `cargo verif`: verify a file's `verif` contracts from the command line.
//!
//! This is the entry point a user reaches for the way they reach for `cargo
//! kani`: one command, a report, and an exit code that says whether every
//! contract held. It is a thin wrapper over `verif::mir::verify::verify_file_with`,
//! so it decides exactly what the library decides -- it does not re-implement a
//! single check.
//!
//! Usage (cargo passes the subcommand name as the first argument):
//!
//! ```console
//! $ cargo verif                       # verifies src/lib.rs of the current crate
//! $ cargo verif --file src/foo.rs     # a specific file
//! $ cargo verif --function add        # one function by name
//! ```
//!
//! Exit codes, kept distinct so a script can tell them apart:
//!
//! * `0` -- every contract held (`FileReport::is_clean`).
//! * `1` -- the frontend ran and found a failure, an incomplete function, a
//!   skipped contract, or a contracted function missing from the MIR. A skipped
//!   function is *not* a pass: its contract could not be read, so it was never
//!   checked.
//! * `2` -- the tool could not run (a missing compiler, an unreadable file, a
//!   compile error). "The tool could not run" must never look like "the code is
//!   wrong", so it is a different code and a different message.

use std::path::{Path, PathBuf};

use verif::mir::verify::{self, FnOutcome};

fn main() {
    let mut file: Option<PathBuf> = None;
    let mut function: Option<String> = None;
    let mut format = String::from("human");
    let mut emit_test: Option<String> = None;
    let mut cache_dir: Option<PathBuf> = None;
    // `cargo verif` invokes this binary as `cargo-verif verif [args]`; drop the
    // subcommand name so a bare `cargo verif --file x` parses. Only the *first*
    // token is stripped, so a value that happens to be `verif` (a cache directory,
    // a function name) survives.
    let mut it = std::env::args().skip(1).peekable();
    if it.peek().is_some_and(|a| a == "verif") {
        it.next();
    }
    while let Some(a) = it.next() {
        match a.as_str() {
            "--file" | "-f" => file = it.next().map(PathBuf::from),
            "--function" | "--fn" => function = it.next(),
            "--format" => format = it.next().unwrap_or_default(),
            "--emit-test" => match it.next() {
                Some(n) => emit_test = Some(n),
                None => {
                    eprintln!("cargo-verif: --emit-test requires a function name");
                    std::process::exit(2);
                }
            },
            "--cache" => cache_dir = it.next().map(PathBuf::from),
            "--help" | "-h" => {
                println!(
                    "cargo verif [--file <path>] [--function <name>]\n\
                     cargo verif [--file <path>] --emit-test <fn>\n\
                     \n\
                     Verifies the `verif` contracts in a Rust source file.\n\
                     Default file: src/lib.rs (then src/main.rs).\n\
                     --emit-test <fn> prints a `#[test]` that reproduces a panic\n\
                     counterexample (it fails while the bug exists, passes once fixed).\n\
                     --cache <dir> reuses decided verdicts across runs when the MIR,\n\
                     the contracts, the edition and the engine are unchanged.\n\
                     Set VERIF_RUSTC to choose the compiler the frontend runs."
                );
                return;
            }
            other if other.starts_with('-') => {
                eprintln!("cargo-verif: unknown flag `{other}` (try --help)");
                std::process::exit(2);
            }
            other => file = Some(PathBuf::from(other)),
        }
    }

    let file = file
        .or_else(|| {
            ["src/lib.rs", "src/main.rs"]
                .iter()
                .map(PathBuf::from)
                .find(|p| p.exists())
        })
        .unwrap_or_else(|| {
            eprintln!("cargo-verif: no file given and neither src/lib.rs nor src/main.rs exists");
            std::process::exit(2);
        });

    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());
    // `--emit-test <fn>` verifies *that* function (even if it has no contract), so
    // replay has a verdict to turn into a test -- an unannotated target would
    // otherwise be skipped and reported as "no counterexample".
    let only: Vec<String> = match &emit_test {
        Some(t) => vec![t.clone()],
        None => function.into_iter().collect(),
    };
    // Make the crate's own dependencies resolvable, so a file that `use`s another
    // crate compiles (C8). `crate_options` returns the default when the crate has no
    // deps or they are not built, so this changes nothing for a single-file file.
    let mut opts = verify::crate_options(&file);
    opts.cache = cache_dir;
    let report = match verify::verify_file_with_opts(&rustc, &file, &only, &opts) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("cargo-verif: could not verify {}: {e}", file.display());
            std::process::exit(2);
        }
    };

    // U3: a counterexample becomes a test. Handled before the format dispatch,
    // because it *replaces* the report with a source file.
    if let Some(name) = emit_test {
        match verify::emit_test_source(&file, &report, &name) {
            Ok(text) => {
                print!("{text}");
                std::process::exit(0);
            }
            Err(reason) => {
                eprintln!("cargo-verif --emit-test: {reason}");
                std::process::exit(2);
            }
        }
    }

    // A requested name that produced no outcome and is not `missing` is a typo, not a
    // clean run: an unmatched `--function`/`--emit-test` would otherwise exit 0.
    for want in &only {
        // Mirror `select`'s matching: the exact label, a `::`-qualified label, or a
        // bare tail. `--function clampish` selects the report's `a::clampish`, so the
        // guard must accept a tail match, not only the exact string.
        let matches = |label: &str| {
            label == want
                || label.ends_with(&format!("::{want}"))
                || label.rsplit("::").next() == Some(want.as_str())
        };
        let named =
            report.outcomes.iter().any(|(n, _)| matches(n)) || report.missing.iter().any(|m| matches(m));
        if !named {
            eprintln!(
                "cargo-verif: `{want}` is not a function in {} (no contract and no body)",
                file.display()
            );
            std::process::exit(2);
        }
    }

    match format.as_str() {
        "human" => print_human(&file, &report),
        "json" => print_json(&file, &report),
        "sarif" => print_sarif(&file, &report),
        other => {
            eprintln!("cargo-verif: unknown --format `{other}` (human | json)");
            std::process::exit(2);
        }
    }

    if !report.is_clean() {
        std::process::exit(1);
    }
}

/// The human report: one line per outcome, then a tally.
fn print_human(file: &Path, report: &verify::FileReport) {
    println!("verifying {}", file.display());
    for (name, outcome) in &report.outcomes {
        let at = report
            .lines
            .get(name)
            .map(|(_, l)| format!("{name}:{l}"))
            .unwrap_or_else(|| name.clone());
        println!("  {at:<28} {}", describe(outcome));
    }
    for m in &report.missing {
        println!("  {m:<28} MISSING (contract carried, but no MIR body found)");
    }
    println!(
        "\n{} verified, {} failed, {} incomplete, {} skipped, {} missing",
        report.verified(),
        report.failed(),
        report.incomplete(),
        report.skipped(),
        report.missing.len()
    );
    println!(
        "{}",
        if report.is_clean() {
            "all contracts held"
        } else {
            "verification did not pass"
        }
    );
}

/// The machine report: a single JSON object, so a CI step can parse it without
/// scraping the human text. Hand-written (the crate is zero-dependency) with the
/// two characters JSON needs escaped -- `"` and `\` -- plus control characters.
fn print_json(file: &Path, report: &verify::FileReport) {
    let mut out = String::from("{\"file\":");
    json_str(&mut out, &file.display().to_string());
    out.push_str(",\"outcomes\":[");
    for (i, (name, outcome)) in report.outcomes.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str("{\"name\":");
        json_str(&mut out, name);
        out.push_str(",\"outcome\":");
        json_str(&mut out, outcome_label(outcome));
        out.push_str(",\"detail\":");
        json_str(&mut out, &describe(outcome));
        out.push('}');
    }
    out.push_str("],\"missing\":[");
    for (i, m) in report.missing.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_str(&mut out, m);
    }
    out.push_str("],\"summary\":{\"verified\":");
    out.push_str(&report.verified().to_string());
    out.push_str(",\"failed\":");
    out.push_str(&report.failed().to_string());
    out.push_str(",\"incomplete\":");
    out.push_str(&report.incomplete().to_string());
    out.push_str(",\"skipped\":");
    out.push_str(&report.skipped().to_string());
    out.push_str(",\"missing\":");
    out.push_str(&report.missing.len().to_string());
    out.push_str(",\"clean\":");
    out.push_str(if report.is_clean() { "true" } else { "false" });
    out.push_str("}}");
    println!("{out}");
}

/// The SARIF 2.1.0 report, so `github/codeql-action/upload-sarif` can annotate a
/// pull request. One `result` per outcome that is *not* `verified` -- a failure
/// is an `error`, an incomplete or skipped function is a `warning` -- each
/// located at the file. A clean run has an empty `results` array, which is what
/// tells code scanning there is nothing to report.
fn print_sarif(file: &Path, report: &verify::FileReport) {
    let mut out = String::from(
        "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",\"version\":\"2.1.0\",\"runs\":[{",
    );
    out.push_str("\"tool\":{\"driver\":{\"name\":\"verif\",\"informationUri\":\"https://github.com/cipansor/verif\",\"rules\":[]}},");
    out.push_str("\"results\":[");
    let mut first = true;
    let mut push = |out: &mut String,
                    rule: &str,
                    level: &str,
                    name: &str,
                    detail: &str,
                    file: &Path,
                    line: Option<usize>| {
        if !first {
            out.push(',');
        }
        first = false;
        out.push_str("{\"ruleId\":");
        json_str(out, rule);
        out.push_str(",\"level\":");
        json_str(out, level);
        out.push_str(",\"message\":{\"text\":");
        json_str(out, &format!("{name}: {detail}"));
        out.push_str("},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":");
        json_str(out, &file.display().to_string());
        out.push('}');
        if let Some(l) = line {
            out.push_str(",\"region\":{\"startLine\":");
            out.push_str(&l.to_string());
            out.push('}');
        }
        out.push_str("}}]}");
    };
    // The line map makes a multi-file crate's findings point at the module a method
    // lives in: `report.lines` carries `(Some(module_file), module_line)`, so a
    // reviewer opening the SARIF lands in the file that actually holds the function.
    // A `None` file (single-file source) falls back to the root `file`.
    let loc = |name: &str| -> (std::path::PathBuf, Option<usize>) {
        match report.lines.get(name) {
            Some((Some(f), l)) => (f.clone(), if *l == 0 { None } else { Some(*l) }),
            Some((None, l)) => (file.to_path_buf(), if *l == 0 { None } else { Some(*l) }),
            None => (file.to_path_buf(), None),
        }
    };
    for (name, outcome) in &report.outcomes {
        match outcome {
            FnOutcome::Verified { .. } => {}
            FnOutcome::Failed { kind, detail } => {
                let (lf, ll) = loc(name);
                push(&mut out, "verif.failed", "error", name, &format!("{kind} — {detail}"), &lf, ll);
            }
            FnOutcome::Incomplete { reasons, .. } => {
                let (lf, ll) = loc(name);
                push(&mut out, "verif.incomplete", "warning", name, &reasons.join("; "), &lf, ll);
            }
            FnOutcome::Skipped { reason } => {
                let (lf, ll) = loc(name);
                push(&mut out, "verif.skipped", "warning", name, reason, &lf, ll);
            }
        }
    }
    for m in &report.missing {
        let (lf, ll) = loc(m);
        push(&mut out, "verif.missing", "warning", m, "contract carried, but no MIR body found", &lf, ll);
    }
    out.push_str("]}]}");
    println!("{out}");
}

/// A short machine label for one outcome.
fn outcome_label(outcome: &FnOutcome) -> &'static str {
    match outcome {
        FnOutcome::Verified { .. } => "verified",
        FnOutcome::Failed { .. } => "failed",
        FnOutcome::Incomplete { .. } => "incomplete",
        FnOutcome::Skipped { .. } => "skipped",
    }
}

/// Append `s` as a JSON string literal (quoted, with `"`, `\` and control
/// characters escaped).
fn json_str(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// One line per outcome, so the `match` lives in a single place.
fn describe(outcome: &FnOutcome) -> String {
    match outcome {
        FnOutcome::Verified { obligations, panics_ruled_out } => {
            format!("verified ({obligations} obligation(s), {panics_ruled_out} panic(s) ruled out)")
        }
        FnOutcome::Failed { kind, detail } => format!("FAILED: {kind} — {detail}"),
        FnOutcome::Incomplete { reasons, .. } => format!("incomplete: {}", reasons.join("; ")),
        FnOutcome::Skipped { reason } => format!("skipped: {reason}"),
    }
}
