//! measurer -- run one command and report its cost, without the launcher's own
//! memory leaking into the figures.
//!
//! Why not `wait4`'s `ru_maxrss`, which is what a Python `os.wait4` harness
//! reads: that value is the child's resident high-water mark *since `fork`*, and
//! `fork` copies the parent's page tables, so the launcher's own RSS becomes a
//! floor under every measurement. Measured: `/bin/true` reports ~5.2 MB through a
//! Python fork/exec runner, because that is Python's own RSS, while this launcher
//! reports ~0.4 MB. The floor is invisible on a build (a `rustc` peaks at ~500 MB)
//! and dominant on a run (a benchmark binary peaks at 2 MB).
//!
//! This launcher reads `/proc/<pid>/status:VmHWM` instead, which belongs to the
//! measured process's own `mm` -- replaced by `exec` -- so it is that program's
//! peak and nothing else. The kernel maintains it as a high-water mark, so the
//! last read before the process exits is its exact peak; the poll only has to
//! outlast the process, not catch the peak in a sample.
//!
//! Without `-t`, only the child is sampled -- correct for running one binary.
//! With `-t`, the whole descendant tree is sampled and the **largest single
//! process's** peak is reported, which is what a `cargo build` figure needs:
//! `cargo` is small, the `rustc`s are its grandchildren, and the largest `rustc`
//! is the build's peak. The tree is found by scanning `/proc` for the parent of
//! each pid, *not* by reading `/proc/<pid>/task/<pid>/children`: cargo spawns
//! `rustc` from a worker **thread**, so the main thread's `children` file is
//! empty and a thread-based walk sees only `cargo` (measured: 34 MB instead of
//! the true 521 MB).
//!
//! Build: `rustc -O -o measurer measurer.rs` (no dependencies, like the crate).
//!
//! Output, one tab-separated line:
//!   code  wall_s  cpu_s  peak_kb  sampled
//! `code` is the child's exit status (127 if it could not be run at all).
//! `sampled` is 0 when the process was too short to sample at all, in which case
//! `peak_kb` is 0 -- reported rather than substituted with the launcher's own
//! floor, so a caller can tell "no data" from "small".
//!
//! The child's stdout/stderr are discarded by default, so a build's noise does
//! not drown the table. That is convenient and it is also how a *failing* build
//! hides -- the launcher reports a wall time either way. Set `MEASURER_SHOW_CHILD`
//! to pass the child's output through, which is what to do when a measurement
//! comes back suspiciously fast.

use std::collections::HashSet;
use std::fs;
use std::mem::MaybeUninit;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// `struct timeval` on Linux: two `long`s. Declared here so this tool needs no
/// crate, like the crate it measures.
#[repr(C)]
#[derive(Clone, Copy)]
struct Timeval {
    sec: i64,
    usec: i64,
}

/// Linux `struct rusage`: two `timeval`s then fifteen `long`s. Only the first
/// two fields are read, but `getrusage` writes the whole struct, so the buffer
/// must be its exact size. The assertion below fails the build if that size is
/// ever wrong, rather than corrupting memory quietly.
#[repr(C)]
struct Rusage {
    utime: Timeval,
    stime: Timeval,
    rest: [i64; 15],
}

const _: () = assert!(std::mem::size_of::<Rusage>() == 152);

// `unsafe extern` is accepted in every edition since Rust 1.82, and required in
// edition 2024; spelling it this way lets the launcher build under either.
unsafe extern "C" {
    fn getrusage(who: i32, usage: *mut Rusage) -> i32;
}
const RUSAGE_CHILDREN: i32 = -1;

/// CPU time (user + sys, seconds) of the children this process has reaped, at
/// microsecond resolution. `/proc/self/stat`'s `cutime`/`cstime` are in clock
/// ticks (10 ms), which is fine for a build and useless for a 3 ms run, so the
/// syscall is used instead. Safe because the buffer is sized by the assertion
/// above and `getrusage` only writes into it.
fn children_cpu_seconds() -> f64 {
    let mut ru = MaybeUninit::<Rusage>::zeroed();
    // SAFETY: `ru` is a correctly-sized, properly-aligned `struct rusage`, and
    // `RUSAGE_CHILDREN` asks only about this process's reaped children.
    let rc = unsafe { getrusage(RUSAGE_CHILDREN, ru.as_mut_ptr()) };
    if rc != 0 {
        return 0.0;
    }
    // SAFETY: `getrusage` returned 0, so it initialised the whole struct.
    let ru = unsafe { ru.assume_init() };
    let t = |v: Timeval| v.sec as f64 + v.usec as f64 / 1e6;
    t(ru.utime) + t(ru.stime)
}

/// A field like `VmHWM:` (kB) from `/proc/<pid>/status`, or `None` if the
/// process is gone or the field is absent.
fn status_field(pid: u32, key: &str) -> Option<u64> {
    let s = fs::read_to_string(format!("/proc/{pid}/status")).ok()?;
    s.lines()
        .find(|l| l.starts_with(key))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|v| v.parse().ok())
}

/// The parent pid of `pid`, from `/proc/<pid>/stat`. Field 4 is the parent, but
/// field 2 is the command in parentheses and may contain spaces, so parse from
/// the last `)`.
fn ppid_of(pid: u32) -> Option<u32> {
    let s = fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    let rp = s.rfind(')')?;
    s[rp + 2..].split_whitespace().nth(1)?.parse().ok()
}

/// Every pid in the tree rooted at `root` (root included), found by scanning
/// `/proc` for parent links -- robust to a parent that spawns from a thread.
fn descendants(root: u32) -> Vec<u32> {
    let mut edges = Vec::new();
    if let Ok(rd) = fs::read_dir("/proc") {
        for e in rd.flatten() {
            if let Ok(pid) = e.file_name().to_string_lossy().parse::<u32>() {
                if let Some(p) = ppid_of(pid) {
                    edges.push((pid, p));
                }
            }
        }
    }
    let mut set: HashSet<u32> = HashSet::from([root]);
    let mut changed = true;
    while changed {
        changed = false;
        for (pid, parent) in &edges {
            if set.contains(parent) && set.insert(*pid) {
                changed = true;
            }
        }
    }
    set.into_iter().collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (tree_mode, cmd) = match args.get(1).map(String::as_str) {
        Some("-t") => (true, &args[2..]),
        _ => (false, &args[1..]),
    };
    if cmd.is_empty() {
        eprintln!("usage: measurer [-t] <cmd> [args...]");
        std::process::exit(2);
    }

    let t0 = Instant::now();
    let quiet = std::env::var_os("MEASURER_SHOW_CHILD").is_none();
    let mut builder = Command::new(&cmd[0]);
    builder.args(&cmd[1..]);
    if quiet {
        builder.stdout(Stdio::null()).stderr(Stdio::null());
    }
    let mut child = match builder.spawn() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("measurer: cannot run {}: {e}", cmd[0]);
            std::process::exit(127);
        }
    };
    let pid = child.id();

    let mut peak = 0u64;
    let mut sampled = false;
    let code;
    loop {
        let pids = if tree_mode { descendants(pid) } else { vec![pid] };
        for p in &pids {
            if let Some(h) = status_field(*p, "VmHWM:") {
                sampled = true;
                if h > peak {
                    peak = h;
                }
            }
        }
        if let Some(status) = child.try_wait().expect("try_wait") {
            code = status.code().unwrap_or(-1);
            break;
        }
        std::thread::sleep(Duration::from_micros(100));
    }

    let wall = t0.elapsed().as_secs_f64();
    let cpu = children_cpu_seconds();
    if !sampled {
        peak = 0;
    }
    println!("{code}\t{wall:.4}\t{cpu:.4}\t{peak}\t{}", u8::from(sampled));
}
