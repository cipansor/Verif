#!/usr/bin/env python3
"""Print (and optionally check) the MIR corpus scoreboard.

`mir_coverage` reports `decided N of M` per corpus file, where `decided` counts the
functions that came back `verified`. This runs it on the three corpora and prints a
markdown table, and -- with `--check` -- fails if any corpus's verified count drops
below the floor recorded in `scripts/scoreboard-floor.txt`.

The floor is a *regression* floor, not a target. The corpora's verdicts are stable
across the toolchains the gate runs (the MIR suite is run under each), so a drop means
a change made a function that used to verify stop verifying -- the kind of regression a
coverage number catches and a green test suite does not. `--write-floor` records the
current counts, which a PR that raises coverage does deliberately.

Usage: python3 scripts/scoreboard.py [--check] [--write-floor]
Exit: 0 printed (and, with --check, all at/above floor); 1 a corpus dropped below its
floor; 2 the scoreboard could not be produced (no compiler, a build error).
"""

import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPORA = [
    "examples/mir_targets/everyday.rs",
    "examples/mir_targets/actuator.rs",
    "examples/mir_targets/realistic.rs",
]
FLOOR = os.path.join(ROOT, "scripts", "scoreboard-floor.txt")


def run(corpus: str) -> tuple[int, int]:
    env = dict(os.environ)
    env.setdefault("VERIF_EDITION", "2024")
    if "VERIF_RUSTC" not in env:
        try:
            env["VERIF_RUSTC"] = subprocess.check_output(
                ["rustup", "which", "rustc"], text=True
            ).strip()
        except (OSError, subprocess.CalledProcessError):
            pass
    out = subprocess.run(
        ["cargo", "run", "-q", "--features", "std", "--example", "mir_coverage", "--", corpus],
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
    )
    match = re.search(r"decided (\d+) of (\d+)", out.stdout)
    if not match:
        print(f"scoreboard: no verdict line for {corpus}\n{out.stderr[-400:]}", file=sys.stderr)
        sys.exit(2)
    return int(match.group(1)), int(match.group(2))


def read_floor() -> dict[str, int]:
    floors: dict[str, int] = {}
    if os.path.exists(FLOOR):
        with open(FLOOR) as handle:
            for line in handle:
                line = line.split("#", 1)[0].strip()
                if not line:
                    continue
                name, count = line.split()
                floors[name] = int(count)
    return floors


def main(argv: list[str]) -> int:
    rows = [(os.path.basename(corpus), *run(corpus)) for corpus in CORPORA]
    print("| corpus | verified | total | share |")
    print("|---|---|---|---|")
    for name, verified, total in rows:
        print(f"| `{name}` | {verified} | {total} | {100 * verified // total}% |")

    # `--check` runs *before* `--write-floor`, so `--check --write-floor` cannot
    # silently lower the baseline: a drop fails (exit 1) without opening the file.
    if "--check" in argv:
        floors = read_floor()
        dropped = [
            (name, verified, floors[name])
            for name, verified, _ in rows
            if name in floors and verified < floors[name]
        ]
        if dropped:
            for name, verified, floor in dropped:
                print(
                    f"scoreboard: {name} dropped to {verified} (floor {floor})",
                    file=sys.stderr,
                )
            return 1
        print("\nscoreboard: every corpus is at or above its floor")

    if "--write-floor" in argv:
        with open(FLOOR, "w") as handle:
            for name, verified, _ in rows:
                handle.write(f"{name} {verified}\n")
        print(f"\nwrote {FLOOR}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
