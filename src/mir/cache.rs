//! The proof cache (U7).
//!
//! A verdict is a *pure* function of the MIR the compiler emitted, the source text
//! (the contracts), the edition and the engine. [`file_key`] hashes all four, so a
//! change to any of them is a cache miss and never a stale hit — the engine is in
//! the key via `VERIF_ENGINE_HASH`, which `build.rs` bakes from `src/**`. That is
//! what makes reuse sound: a cached `verified` cannot survive a change to the rule
//! that produced it.
//!
//! Only `Verified` and `Failed` are stored. They carry no arena handles, so a
//! cached copy is the whole answer. `Incomplete` is re-derived every run — it holds
//! a `MirReport` whose obligations are term ids into an arena that is gone — and
//! `Skipped` is cheap.

use std::collections::BTreeMap;
use std::path::Path;

use super::verify::FnOutcome;

/// The engine hash `build.rs` baked in.
pub fn engine_hash() -> &'static str {
    env!("VERIF_ENGINE_HASH")
}

/// A decided outcome, free of arena handles so it can be stored and reloaded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cached {
    /// Every obligation proved.
    Verified {
        /// Obligations discharged.
        obligations: usize,
        /// Rustc-emitted panic conditions ruled out.
        panics_ruled_out: usize,
    },
    /// A definite failure.
    Failed {
        /// Which obligation failed.
        kind: String,
        /// The counterexample.
        detail: String,
    },
}

impl Cached {
    /// The `FnOutcome` a cache hit stands for.
    pub fn to_outcome(&self) -> FnOutcome {
        match self {
            Cached::Verified { obligations, panics_ruled_out } => FnOutcome::Verified {
                obligations: *obligations,
                panics_ruled_out: *panics_ruled_out,
            },
            Cached::Failed { kind, detail } => FnOutcome::Failed {
                kind: kind.clone(),
                detail: detail.clone(),
            },
        }
    }

    /// The cache form of a fresh outcome, or `None` for one that is not cached
    /// (`Incomplete`, `Skipped`).
    pub fn of(outcome: &FnOutcome) -> Option<Cached> {
        match outcome {
            FnOutcome::Verified { obligations, panics_ruled_out } => Some(Cached::Verified {
                obligations: *obligations,
                panics_ruled_out: *panics_ruled_out,
            }),
            FnOutcome::Failed { kind, detail } => Some(Cached::Failed {
                kind: kind.clone(),
                detail: detail.clone(),
            }),
            _ => None,
        }
    }
}

/// The cached outcomes for one file, keyed by report name.
pub type Entries = BTreeMap<String, Cached>;

/// A key over everything a verdict depends on: the whole file's MIR, the source
/// text, the edition and the engine hash.
///
/// Coarse (the whole file) on purpose: a change to one function re-verifies the
/// file, which is sound and simple, rather than a per-function key that could miss
/// a dependency two functions share.
pub fn file_key(mir: &str, source: &str, edition: &str) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for part in [mir, source, edition, engine_hash()] {
        for b in part.as_bytes() {
            h ^= *b as u64;
            h = h.wrapping_mul(0x100_0000_01b3);
        }
        // A separator, so two parts cannot concatenate into one.
        h ^= 0xff;
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    format!("{h:016x}")
}

/// Read the cache entry for `key` under `dir`. A missing or unreadable entry is an
/// empty map (a miss), never an error: a broken cache must not stop a verification.
pub fn load(dir: &Path, key: &str) -> Entries {
    let mut out = Entries::new();
    let Ok(text) = std::fs::read_to_string(dir.join(key)) else { return out };
    for line in text.lines() {
        let f: Vec<&str> = line.split('\t').collect();
        match f.as_slice() {
            ["V", name, o, p] => {
                if let (Ok(o), Ok(p)) = (o.parse(), p.parse()) {
                    out.insert(
                        unescape(name),
                        Cached::Verified { obligations: o, panics_ruled_out: p },
                    );
                }
            }
            ["F", name, kind, detail] => {
                out.insert(
                    unescape(name),
                    Cached::Failed { kind: unescape(kind), detail: unescape(detail) },
                );
            }
            _ => {}
        }
    }
    out
}

/// Write the cache entry for `key` under `dir`.
pub fn store(dir: &Path, key: &str, entries: &Entries) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let mut text = String::new();
    for (name, c) in entries {
        match c {
            Cached::Verified { obligations, panics_ruled_out } => {
                text.push_str(&format!(
                    "V\t{}\t{}\t{}\n",
                    escape(name),
                    obligations,
                    panics_ruled_out
                ));
            }
            Cached::Failed { kind, detail } => {
                text.push_str(&format!(
                    "F\t{}\t{}\t{}\n",
                    escape(name),
                    escape(kind),
                    escape(detail)
                ));
            }
        }
    }
    std::fs::write(dir.join(key), text)
}

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('\t', "\\t").replace('\n', "\\n")
}

fn unescape(s: &str) -> String {
    let mut out = String::new();
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c == '\\' {
            match it.next() {
                Some('t') => out.push('\t'),
                Some('n') => out.push('\n'),
                Some('\\') => out.push('\\'),
                Some(o) => {
                    out.push('\\');
                    out.push(o);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every input that affects a verdict must be in the key, or a stale hit is
    /// possible. The engine hash is constant within a build, so it cannot be varied
    /// here, but it is one of the four parts [`file_key`] folds in.
    #[test]
    fn the_key_changes_with_every_input() {
        let base = file_key("mir", "src", "Rust2024");
        assert_ne!(base, file_key("mir2", "src", "Rust2024"), "the MIR is in the key");
        assert_ne!(base, file_key("mir", "src2", "Rust2024"), "the source is in the key");
        assert_ne!(base, file_key("mir", "src", "Rust2021"), "the edition is in the key");
        assert_eq!(base, file_key("mir", "src", "Rust2024"), "same inputs, same key");
    }

    /// A tab or newline in a name/kind/detail must round-trip through the line format.
    #[test]
    fn a_tab_and_newline_round_trip_through_escape() {
        for s in ["plain", "a\tb", "a\nb", "a\\b"] {
            assert_eq!(unescape(&escape(s)), s, "round trip for {s:?}");
        }
    }
}
