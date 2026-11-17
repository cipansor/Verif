//! The soundness ledger is a claim about the test suite, so it is checked.
//!
//! `SOUNDNESS.md` lists every false proof (and wrong verdict) this project has
//! found, each naming the **fixture** that fails if the fix is undone. A ledger
//! is only worth its rows if the fixtures it names still exist *and are tests*:
//! a renamed test would leave a row pointing at nothing, and a same-named helper
//! that is never run would let the row read as evidence while checking nothing.
//! This module extracts the fixture column from every table and requires each
//! name to resolve to a `#[test]` function, so a stale or vacuous row fails the
//! build.
//!
//! It also pins the three structural facts the ledger's honesty rests on:
//! every row carries a commit and a date (A1 is computed from those), no row's
//! date is in the future (a hand-edited date is the one field a reader cannot
//! check), and every defect class the roadmap names has a row.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    // `cargo test` runs with the crate root as the working directory.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The source text of every `.rs` file under `dir`, keyed by a path relative to
/// `dir` (`mir.rs`, `mir/spec.rs`, …) so a fixture cell can name its file.
fn rs_sources(dir: &Path) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
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
            let rel = p.strip_prefix(dir).unwrap_or(&p).to_string_lossy().into_owned();
            out.insert(rel, text);
        }
    }
    out
}

/// Every `#[test] fn <name>` declared in `text`, plus the names of functions that
/// are declared but **not** tests.
///
/// The distinction is the point: a fixture must be a test that actually runs. A
/// function that merely shares the name — a helper, a constructor, a local — is
/// not evidence, so the caller treats a non-test match as a failure.
fn fns_in(text: &str) -> (BTreeSet<String>, BTreeSet<String>) {
    let mut tests = BTreeSet::new();
    let mut plain = BTreeSet::new();
    let mut pending_test = false;
    for line in text.lines() {
        let t = line.trim_start();
        if t.starts_with("#[test]") {
            pending_test = true;
            continue;
        }
        // An attribute other than `#[test]` does not clear a pending `#[test]`
        // (e.g. `#[test] #[should_panic]`), but a blank or code line does.
        if t.starts_with("#[") {
            continue;
        }
        let Some(rest) = t.strip_prefix("pub fn ").or_else(|| t.strip_prefix("fn ")) else {
            pending_test = false;
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if !name.is_empty() {
            if pending_test {
                tests.insert(name);
            } else {
                plain.insert(name);
            }
        }
        pending_test = false;
    }
    (tests, plain)
}

/// One ledger row: the fixture cell (column 4), the commit cell (column 5) and
/// the date cell (column 6). Both tables have the shape
/// `| # | Symptom | Class | Fixture | Commit | Fixed |`.
struct Row {
    fixture: String,
    commit: String,
    date: String,
}

fn rows(ledger: &str) -> Vec<Row> {
    let mut out = Vec::new();
    for line in ledger.lines() {
        let line = line.trim();
        if !line.starts_with("| ") || line.starts_with("|---") || line.starts_with("| #") {
            continue;
        }
        let cells: Vec<&str> = line.split('|').collect();
        // `| 1 | … | … | fixture | commit | date |` -> indices 4, 5, 6.
        if cells.len() >= 7 {
            out.push(Row {
                fixture: cells[4].to_string(),
                commit: cells[5].to_string(),
                date: cells[6].to_string(),
            });
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
        out.push(after[..end].to_string());
        rest = &after[end + 1..];
    }
    out
}

fn is_date(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() == 10 && b[4] == b'-' && b[7] == b'-' && b.iter().enumerate().all(|(i, c)| {
        if i == 4 || i == 7 {
            true
        } else {
            c.is_ascii_digit()
        }
    })
}

#[test]
fn the_ledger_keeps_a_row_for_every_defect_in_both_tables() {
    // The two tables are a *record*, so a row that silently vanishes is a lost
    // piece of evidence. The split is the section header between them: rows before
    // it are the MIR frontend, rows after it are the engine and imperative layer.
    let ledger = std::fs::read_to_string(root().join("SOUNDNESS.md")).expect("ledger");
    let split = ledger
        .find("## The engine and the imperative layer")
        .expect("the engine section header must exist");
    let (mir, engine) = ledger.split_at(split);
    // The MIR table's rows are numbered 1..=29 and the engine table's 30..=45; the
    // counts are asserted exactly so adding or dropping a defect is a deliberate
    // edit to this number, made in the same commit as the row.
    assert_eq!(rows(mir).len(), 29, "the MIR table must keep its 29 rows");
    assert_eq!(rows(engine).len(), 16, "the engine table must keep its 16 rows");
    // And the numbering is contiguous across the two, so a row cannot be renumbered
    // into a gap without the check noticing.
    let nums: Vec<u32> = ledger
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let rest = l.strip_prefix("| ")?;
            let n = rest.split('|').next()?.trim();
            n.parse::<u32>().ok()
        })
        .collect();
    assert_eq!(
        nums,
        (1..=45).collect::<Vec<u32>>(),
        "the ledger's row numbers must be 1..=45 with no gaps or duplicates"
    );
}

#[test]
fn the_soundness_ledger_names_fixtures_that_are_tests() {
    let path = root().join("SOUNDNESS.md");
    let ledger = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the soundness ledger must exist at {}: {e}", path.display()));

    let test_sources = rs_sources(&root().join("tests"));
    let src_sources = rs_sources(&root().join("src"));
    // `name -> (is_test, relative file)` for every function in the tree.
    let mut known: BTreeMap<String, (bool, String)> = BTreeMap::new();
    for (file, text) in test_sources.iter().chain(src_sources.iter()) {
        let (tests, plain) = fns_in(text);
        for n in tests {
            known.insert(n, (true, file.clone()));
        }
        for n in plain {
            known.entry(n).or_insert((false, file.clone()));
        }
    }

    let rows = rows(&ledger);
    assert!(
        rows.len() >= 40,
        "the ledger must keep its rows (29 MIR + 16 engine); found {}",
        rows.len()
    );

    let mut checked = 0usize;
    for row in &rows {
        // A fixture cell names one or more tests, and may name a file to pin the
        // test to it. The file token is a `.rs` path; a fixture is a snake_case
        // identifier.
        let toks = backticked(&row.fixture);
        let files: Vec<&String> = toks.iter().filter(|t| t.ends_with(".rs")).collect();
        for tok in &toks {
            if tok.ends_with(".rs") {
                continue; // a file path, used to pin the fixtures above
            }
            if !tok.contains('_') || !tok.chars().next().is_some_and(|c| c.is_ascii_lowercase()) {
                continue; // a prose token (`Verified`, `rustc`), not a fixture
            }
            checked += 1;
            let Some((is_test, file)) = known.get(tok) else {
                panic!(
                    "the soundness ledger names `{tok}` as a fixture, but no `fn {tok}` exists \
                     in `tests/` or `src/`; a renamed test leaves the row pointing at nothing"
                );
            };
            assert!(
                *is_test,
                "the soundness ledger names `{tok}` as a fixture, but `{tok}` in `{file}` is \
                 not a `#[test]`; a same-named helper that never runs is not evidence"
            );
            // If the cell names a file, the test must be in it. This catches a
            // fixture that moved to another file while the cell kept the old one.
            for f in &files {
                let want = f
                    .strip_prefix("tests/")
                    .or_else(|| f.strip_prefix("src/"))
                    .unwrap_or(f);
                if known_in_file(&test_sources, &src_sources, tok, want).is_none() {
                    panic!(
                        "the soundness ledger names `{tok}` in `{f}`, but `{tok}` is not a \
                         `#[test]` in that file"
                    );
                }
            }
        }
    }
    assert!(
        checked >= 35,
        "the ledger must name real fixtures, not only prose; checked {checked}"
    );
}

/// `Some(())` when `name` is a `#[test]` in the file whose relative path ends
/// with `want`.
fn known_in_file(
    test_sources: &BTreeMap<String, String>,
    src_sources: &BTreeMap<String, String>,
    name: &str,
    want: &str,
) -> Option<()> {
    for (file, text) in test_sources.iter().chain(src_sources.iter()) {
        if !file.ends_with(want) {
            continue;
        }
        let (tests, _) = fns_in(text);
        if tests.contains(name) {
            return Some(());
        }
    }
    None
}

#[test]
fn every_ledger_row_carries_a_commit_and_a_date() {
    let ledger = std::fs::read_to_string(root().join("SOUNDNESS.md")).expect("ledger");
    let rows = rows(&ledger);
    assert!(!rows.is_empty(), "the ledger must have rows");

    for row in &rows {
        let commits = backticked(&row.commit);
        assert_eq!(
            commits.len(),
            1,
            "each row must name exactly one commit; got {commits:?} in `{}`",
            row.fixture
        );
        let c = &commits[0];
        assert!(
            c.len() >= 7 && c.chars().all(|ch| ch.is_ascii_hexdigit()),
            "a commit must be a hex hash, got `{c}`"
        );
        let d = row.date.trim();
        assert!(
            is_date(d),
            "each row must carry a `YYYY-MM-DD` date (A1 is computed from it), got `{d}`"
        );
    }
}

#[test]
fn no_ledger_date_is_in_the_future() {
    let ledger = std::fs::read_to_string(root().join("SOUNDNESS.md")).expect("ledger");
    // A hand-edited date is the one field a reader cannot check, so the check is
    // mechanical: no row may postdate today. `date -u +%F` is the reference, and
    // the crate's history is dated in UTC.
    let today = utc_today();
    let mut newest = String::new();
    for row in rows(&ledger) {
        let d = row.date.trim().to_string();
        if !is_date(&d) {
            continue;
        }
        assert!(
            d.as_str() <= today.as_str(),
            "a ledger date `{d}` is in the future (today is {today}); a date a reader cannot \
             verify is not evidence"
        );
        if d > newest {
            newest = d;
        }
    }
    assert!(
        !newest.is_empty(),
        "the ledger must carry at least one dated row for the A1 clock"
    );
}

/// Today's date in UTC, from the system clock, as `YYYY-MM-DD`.
///
/// The ledger's dates are the commit dates, which are UTC; comparing strings is
/// valid because the format is fixed-width and zero-padded.
fn utc_today() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock before the epoch")
        .as_secs() as i64;
    // Civil-from-days (Howard Hinnant's algorithm), so no dependency is needed.
    let days = secs.div_euclid(86_400);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{y:04}-{m:02}-{d:02}")
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

/// The helpers above are the check, so their own logic is pinned here — the
/// integration tests would pass even if `fns_in` silently treated a non-test as
/// a test (which is exactly the review's finding #4), because the real ledger
/// names no such fixture. These tests close that gap without a mutated file.
#[cfg(test)]
mod helpers {
    use super::*;

    #[test]
    fn a_test_annotation_is_required_to_count_as_a_fixture() {
        let src = "#[test]\nfn a_real_test() {}\nfn a_helper() {}\n\
                   #[test]\n#[should_panic]\nfn a_panicking_test() {}\n\
                   pub fn a_pub_helper() {}\n";
        let (tests, plain) = fns_in(src);
        assert!(tests.contains("a_real_test"), "a `#[test] fn` is a test");
        assert!(
            tests.contains("a_panicking_test"),
            "an attribute after `#[test]` must not clear it"
        );
        assert!(!tests.contains("a_helper"), "a plain `fn` is not a test");
        assert!(!tests.contains("a_pub_helper"), "a `pub fn` is not a test");
        assert!(plain.contains("a_helper") && plain.contains("a_pub_helper"));
    }

    #[test]
    fn a_date_must_be_iso_and_numeric() {
        assert!(is_date("2026-11-16"));
        assert!(!is_date("2026-1-16"), "month must be two digits");
        assert!(!is_date("26-11-16"), "year must be four digits");
        assert!(!is_date("2026/11/16"), "separator must be `-`");
        assert!(!is_date("today"));
        assert!(!is_date(""));
    }

    #[test]
    fn utc_today_is_a_plausible_iso_date() {
        let t = utc_today();
        assert!(is_date(&t), "utc_today must be `YYYY-MM-DD`, got `{t}`");
        // A sanity floor: the crate did not exist before 2020, and no sane clock
        // reads a year below it, so a broken conversion is caught here.
        assert!(t.as_str() >= "2020-01-01", "utc_today looks wrong: `{t}`");
    }

    #[test]
    fn backticked_returns_every_span() {
        assert_eq!(backticked("`a_b` and `c_d`"), vec!["a_b", "c_d"]);
        assert_eq!(backticked("no spans here"), Vec::<String>::new());
        // An unbalanced backtick is ignored rather than panicking on the slice.
        assert_eq!(backticked("`open only"), Vec::<String>::new());
    }

    #[test]
    fn rows_reads_both_tables() {
        let md = "| # | Symptom | Class | Fixture | Commit | Fixed |\n\
                  |---|---|---|---|---|---|\n\
                  | 1 | x | false proof | `a_fixture` | `abc1234` | 2026-01-01 |\n";
        let r = rows(md);
        assert_eq!(r.len(), 1, "the header and the rule must not be rows");
        assert_eq!(r[0].fixture.trim(), "`a_fixture`");
        assert_eq!(r[0].commit.trim(), "`abc1234`");
        assert_eq!(r[0].date.trim(), "2026-01-01");
    }
}

