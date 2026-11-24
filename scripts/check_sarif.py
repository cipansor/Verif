#!/usr/bin/env python3
"""Fail if a SARIF report from `cargo verif` is not well-formed, or does not name an
expected function.

The reusable GitHub Action (`.github/actions/verif`) uploads the SARIF to code
scanning, so the file is what a reviewer actually sees. A malformed file is not a
failed check but *no* check, so this asserts the shape the uploader requires:
SARIF 2.1.0, one `verif` run, every result carrying a `level`, a message, and a
location with a `>= 1` line and a URI. It also asserts each function named on the
command line appears in the results -- so a run that silently reports nothing (a
dropped function, an empty result set) fails here rather than passing.

Usage: python3 scripts/check_sarif.py <report.sarif> [expected-function ...]
Exit: 0 well-formed and every expected function named; 1 otherwise; 2 usage/read error.
"""

import json
import sys


def fail(message: str) -> int:
    print(f"check_sarif: {message}", file=sys.stderr)
    return 1


def main(argv: list[str]) -> int:
    # Optional `--root <path>`: assert that per-file attribution works -- at least one
    # result points at a file OTHER than the root (a module file), with a positive line.
    root = None
    rest: list[str] = []
    i = 0
    while i < len(argv):
        if argv[i] == "--root" and i + 1 < len(argv):
            root = argv[i + 1]
            i += 2
        else:
            rest.append(argv[i])
            i += 1
    if not rest:
        print("usage: check_sarif.py [--root PATH] <report.sarif> [expected-function ...]", file=sys.stderr)
        return 2
    path, expected = rest[0], rest[1:]
    try:
        with open(path) as handle:
            data = json.load(handle)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"check_sarif: cannot read {path}: {exc}", file=sys.stderr)
        return 2

    if data.get("version") != "2.1.0":
        return fail(f"version is {data.get('version')!r}, expected '2.1.0'")
    if "sarif-2.1.0" not in str(data.get("$schema", "")):
        return fail(f"$schema is {data.get('$schema')!r}, expected the SARIF 2.1.0 schema")
    runs = data.get("runs")
    if not runs:
        return fail("no `runs` array, or it is empty")
    run = runs[0]
    driver = run.get("tool", {}).get("driver", {})
    if driver.get("name") != "verif":
        return fail(f"tool.driver.name is {driver.get('name')!r}, expected 'verif'")

    names: set[str] = set()
    levels: dict[str, set[str]] = {}
    for index, result in enumerate(run.get("results", [])):
        if result.get("level") not in ("error", "warning", "note"):
            return fail(f"result {index} has no valid `level`")
        text = result.get("message", {}).get("text")
        if not text:
            return fail(f"result {index} has no message text")
        name = text.split(":", 1)[0].strip()
        names.add(name)
        levels.setdefault(name, set()).add(result.get("level"))
        locations = result.get("locations")
        if not locations:
            return fail(f"result {index} has no location")
        physical = locations[0].get("physicalLocation", {})
        if physical.get("region", {}).get("startLine", 0) < 1:
            return fail(f"result {index} has no positive `startLine`")
        if not physical.get("artifactLocation", {}).get("uri"):
            return fail(f"result {index} has no artifact URI")

    if root is not None:
        import os

        root_norm = os.path.normpath(root)

        def uri_of(result: dict) -> str:
            return result.get("locations", [{}])[0].get("physicalLocation", {}).get("artifactLocation", {}).get("uri", "")

        module_results = [r for r in run.get("results", []) if os.path.normpath(uri_of(r)) != root_norm]
        if not module_results:
            return fail(
                f"--root {root}: no result points at a module file; per-file attribution is broken"
            )
        for r in module_results:
            if r.get("locations", [{}])[0].get("physicalLocation", {}).get("region", {}).get("startLine", 0) < 1:
                return fail("a module-file result has no positive `startLine`")

    missing = [name for name in expected if name not in names]
    if missing:
        return fail(f"the report does not name {missing}; it names {sorted(names)}")

    # An expected function must be reported as an *error* (a refutation). A skipped
    # or undecided function is a `note`/`warning`, and accepting one would let the
    # smoke test pass without the verifier refuting anything.
    for name in expected:
        if "error" not in levels.get(name, set()):
            return fail(
                f"`{name}` is reported at level {sorted(levels.get(name, set()))}, not "
                f"`error`; a skipped/undecided function must not pass as a refutation"
            )

    print(f"sarif: {len(run.get('results', []))} result(s), naming {sorted(names)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
