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
    if not argv:
        print("usage: check_sarif.py <report.sarif> [expected-function ...]", file=sys.stderr)
        return 2
    path, expected = argv[0], argv[1:]
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
    for index, result in enumerate(run.get("results", [])):
        if result.get("level") not in ("error", "warning", "note"):
            return fail(f"result {index} has no valid `level`")
        text = result.get("message", {}).get("text")
        if not text:
            return fail(f"result {index} has no message text")
        names.add(text.split(":", 1)[0].strip())
        locations = result.get("locations")
        if not locations:
            return fail(f"result {index} has no location")
        physical = locations[0].get("physicalLocation", {})
        if physical.get("region", {}).get("startLine", 0) < 1:
            return fail(f"result {index} has no positive `startLine`")
        if not physical.get("artifactLocation", {}).get("uri"):
            return fail(f"result {index} has no artifact URI")

    missing = [name for name in expected if name not in names]
    if missing:
        return fail(f"the report does not name {missing}; it names {sorted(names)}")

    print(f"sarif: {len(run.get('results', []))} result(s), naming {sorted(names)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
