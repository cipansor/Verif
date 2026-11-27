//! Coverage probe: run the frontend over **every function of a real crate's MIR**.
//!
//! `mir_coverage` answers "how much of our own corpus decides"; this answers "how
//! much of a crate we did not write decides", which is where the frontend's real
//! gaps show up. It needs the crate's textual MIR dump, so the two-step is:
//!
//! ```console
//! $ rustc --crate-type=lib --edition 2021 --emit=mir -o /tmp/c.mir src/lib.rs
//! $ PROBE_CFGS='feature="std",feature="default"' \
//!     cargo run --release --features std --example real_probe -- src/lib.rs /tmp/c.mir
//! ```
//!
//! `PROBE_CFGS` mirrors the `--cfg`s the crate was compiled with, so the reader's
//! `#[cfg]` answers are the compiler's. `PROBE_ONLY=<substr>` filters by function
//! name, `PROBE_LIMIT` caps the count, and `PROBE_ENUMS=1` dumps each function's
//! structs, arguments and seeded field paths -- the fastest way to see *why* a
//! `length_of`/field read came back unknown.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::time::Instant;

use verif::mir::spec;
use verif::mir::verify::{self, FnOutcome};

fn main() {
    let mut args = std::env::args().skip(1);
    let src = args.next().expect("source path");
    let mir_path = args.next().expect("mir dump path");
    let limit: usize = args.next().and_then(|s| s.parse().ok()).unwrap_or(usize::MAX);
    let text = std::fs::read_to_string(&src).unwrap();
    // `PROBE_CFGS='feature="std",feature="default"'` mirrors what `crate_options`
    // passes to rustc, so the reader sees the same `#[cfg]` answers the compiler did.
    let mut cfgs: Vec<String> = Vec::new();
    for c in std::env::var("PROBE_CFGS").unwrap_or_default().split(',') {
        let c = c.trim();
        if !c.is_empty() {
            cfgs.push("--cfg".to_string());
            cfgs.push(c.to_string());
        }
    }
    let specs = spec::extract_crate_with_cfgs(Path::new(&src), &text, &cfgs);
    if std::env::var_os("PROBE_ENUMS").is_some() {
        eprintln!("enums: {:?}", specs.enums.keys().collect::<Vec<_>>());
        eprintln!("structs: {:?}", specs.structs.keys().collect::<Vec<_>>());
        eprintln!("by_fn: {:?}", specs.by_fn.keys().take(5).collect::<Vec<_>>());
        for (k, v) in &specs.enums {
            eprintln!("enum {k}: {:?}", v.variants);
        }

    }
    let mir = std::fs::read_to_string(&mir_path).unwrap();
    let names = verify::function_names(&mir);
    if std::env::var_os("PROBE_ENUMS").is_some() {
        for (k, v) in &specs.structs {
            eprintln!("struct {k}: {:?}", v.fields);
        }
        let fns = verify::functions(&mir);
        for (name, f) in fns.iter() {
            let tys: Vec<_> = f.arg_locals.iter().map(|l| f.ty_of(*l).cloned()).collect();
            let fe = spec::field_env_named(f, None, &specs.structs, &specs.enums);
            eprintln!("fn {name}: args={tys:?} fields={:?} lens={:?}", fe.seeds, fe.path_len_seeds);
        }
    }
    eprintln!("parsed {} functions", names.len());
    let mut tally: BTreeMap<String, usize> = BTreeMap::new();
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    let started = Instant::now();
    // `PROBE_ONLY=substr` restricts the run to the functions whose name contains it,
    // which is how a single impl block is probed without a five-minute full sweep.
    let only = std::env::var("PROBE_ONLY").ok();
    for (i, name) in names.iter().enumerate() {
        if i >= limit {
            break;
        }
        if let Some(only) = &only {
            if !name.contains(only.as_str()) {
                continue;
            }
        }
        let t = Instant::now();
        let report = verify::verify_mir_text(&mir, &specs, std::slice::from_ref(name)).unwrap();
        let Some((_, outcome)) = report.outcomes.first() else {
            continue;
        };
        let (tag, detail) = match outcome {
            FnOutcome::Verified { .. } => ("verified".to_string(), String::new()),
            FnOutcome::Failed { kind, .. } => ("failed".to_string(), kind.clone()),
            FnOutcome::Incomplete { reasons, .. } => (
                "incomplete".to_string(),
                reasons.first().cloned().unwrap_or_default(),
            ),
            FnOutcome::Skipped { reason } => ("skipped".to_string(), reason.clone()),
        };
        *tally.entry(tag.clone()).or_default() += 1;
        if !detail.is_empty() {
            *reasons.entry(format!("{tag}: {}", normalize(&detail))).or_default() += 1;
        }
        println!(
            "{:<90} {:<11} {:>7.2}s  {}",
            name.chars().take(90).collect::<String>(),
            tag,
            t.elapsed().as_secs_f64(),
            detail.chars().take(120).collect::<String>()
        );
        std::io::stdout().flush().ok();
    }
    eprintln!("\n=== tally ({:.1}s) ===", started.elapsed().as_secs_f64());
    for (k, v) in &tally {
        eprintln!("{k:<12} {v}");
    }
    eprintln!("\n=== top reasons ===");
    let mut rs: Vec<_> = reasons.into_iter().collect();
    rs.sort_by_key(|&(_, n)| std::cmp::Reverse(n));
    for (k, v) in rs.into_iter().take(40) {
        eprintln!("{v:>5}  {k}");
    }
}

/// Collapse digits and quoted names so the same reason from different functions
/// groups together.
fn normalize(s: &str) -> String {
    let mut out = String::new();
    let mut in_num = false;
    for c in s.chars() {
        if c.is_ascii_digit() {
            if !in_num {
                out.push('N');
                in_num = true;
            }
        } else {
            in_num = false;
            out.push(c);
        }
    }
    out.chars().take(160).collect()
}
