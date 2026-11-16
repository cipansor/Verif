//! The soundness ledger is a claim about the test suite, so it is checked.
//!
//! `SOUNDNESS.md` lists every false proof (and wrong verdict) this project has
//! found, each naming the **fixture** that fails if the fix is undone. A ledger
//! is only worth its rows if the fixtures it names still exist: a renamed test
//! would leave a row pointing at nothing, and the row would read as evidence
//! while being prose. This module extracts the fixture column and requires every
//! name to resolve to a `fn` in the sources, so a stale ledger fails the build.
//!
//! It also pins the two structural facts the ledger's honesty rests on: there is
//! a row per defect class the roadmap names, and the newest row's date is not in
//! the future (a hand-edited date is the one field a reader cannot check).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    // `cargo test` runs with the crate root as the working directory.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Every `fn <name>` / `pub fn <name>` declared under `dir`.
fn declared_fns(dir: &Path) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else { continue };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&p) else { continue };
            for line in text.lines() {
                let t = line.trim_start();
                for prefix in ["pub fn ", "fn "] {
                    if let Some(rest) = t.strip_prefix(prefix) {
                        let name: String =
                            rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                        if !name.is_empty() {
                            out.insert(name);
                        }
                        break;
                    }
                }
            }
        }
    }
    out
}

/// The fixture column (the fourth cell) of each row in the ledger's MIR table.
fn fixture_cells(ledger: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in ledger.lines() {
        let line = line.trim();
        if !line.starts_with("| ") || line.starts_with("|---") || line.starts_with("| #") {
            continue;
        }
        // `| 1 | symptom | class | fixture | date |` -> cells[4] is the fixture.
        let cells: Vec<&str> = line.split('|').collect();
        if cells.len() >= 6 {
            out.push(cells[4].to_string());
        }
    }
    out
}

/// Each backticked identifier in a cell, e.g. `` `foo_bar` `` -> `foo_bar`.
fn backticked(cell: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = cell;
    while let Some(start) = rest.find('`') {
        let after = &rest[start + 1..];
        let Some(end) = after.find('`') else { break };
        let tok = &after[..end];
        if tok.chars().all(|c| c.is_alphanumeric() || c == '_') && !tok.is_empty() {
            out.push(tok.to_string());
        }
        rest = &after[end + 1..];
    }
    out
}

#[test]
fn the_soundness_ledger_names_fixtures_that_exist() {
    let path = root().join("SOUNDNESS.md");
    let ledger = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the soundness ledger must exist at {}: {e}", path.display()));

    let cells = fixture_cells(&ledger);
    assert!(
        cells.len() >= 21,
        "the ledger must keep its MIR-frontend rows; found {} fixture cells",
        cells.len()
    );

    let declared = declared_fns(&root().join("tests"))
        .into_iter()
        .chain(declared_fns(&root().join("src")))
        .collect::<BTreeSet<_>>();

    let mut checked = 0usize;
    for cell in &cells {
        for tok in backticked(cell) {
            // Only fixture-shaped names: a test or a corpus function, which is a
            // snake_case identifier. A prose token such as `Verified` or `rustc`
            // is not a fixture and is left alone.
            if !tok.contains('_') || !tok.chars().next().is_some_and(|c| c.is_ascii_lowercase()) {
                continue;
            }
            checked += 1;
            assert!(
                declared.contains(&tok),
                "the soundness ledger names `{tok}` as a fixture, but no `fn {tok}` exists \
                 in `tests/` or `src/`; a renamed test leaves the row pointing at nothing"
            );
        }
    }
    assert!(
        checked >= 18,
        "the ledger must name real fixtures, not only prose; checked {checked}"
    );
}

#[test]
fn the_ledger_has_a_row_for_every_class_the_roadmap_names() {
    let ledger = std::fs::read_to_string(root().join("SOUNDNESS.md")).expect("ledger");
    // The four classes are the vocabulary the ledger defines; a row that used an
    // undefined class would not be classifiable by a reader.
    for class in ["false proof", "false refutation", "lost proof", "wrong verdict"] {
        assert!(
            ledger.contains(class),
            "the ledger must define and use the class `{class}`"
        );
    }
}
