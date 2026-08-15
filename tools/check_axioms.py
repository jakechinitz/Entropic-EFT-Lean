#!/usr/bin/env python3
"""Check the axiom footprint emitted by `Scripts/AxiomAudit.lean`.

Usage:
    lake env lean Scripts/AxiomAudit.lean > axiom-footprint.txt
    python tools/check_axioms.py axiom-footprint.txt

Fails (exit 1) if any audited theorem depends on an axiom outside the declared
trust base, or if the audit produced no output at all (which would silently
turn this check into a no-op).

Trust base:
  propext, Classical.choice, Quot.sound   standard Lean/Mathlib foundations
  Lean.ofReduceBool                       `native_decide`: compiled evaluation of a
                                          finite enumeration, not kernel reduction

`sorryAx` — what a `sorry` introduces — is deliberately NOT in the allowlist.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ALLOWED = {
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.ofReduceBool",
}

# "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]"
DEPENDS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
# "'Foo.bar' does not depend on any axioms"
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_axioms.py <axiom-footprint.txt>", file=sys.stderr)
        return 2

    text = Path(argv[1]).read_text()

    audited: list[tuple[str, set[str]]] = []
    for m in NO_AXIOMS.finditer(text):
        audited.append((m.group(1), set()))
    for m in DEPENDS.finditer(text):
        axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
        audited.append((m.group(1), axioms))

    if not audited:
        print("FAIL: no `#print axioms` output found — the audit did not run.")
        print("----- captured output -----")
        print(text)
        return 1

    failures: list[str] = []
    for name, axioms in sorted(audited):
        extra = axioms - ALLOWED
        status = "OK  " if not extra else "FAIL"
        rendered = ", ".join(sorted(axioms)) if axioms else "(none)"
        print(f"{status} {name}: {rendered}")
        if extra:
            failures.append(f"{name} depends on disallowed axiom(s): {', '.join(sorted(extra))}")

    print()
    print(f"audited {len(audited)} declarations")

    if failures:
        print()
        for f in failures:
            print(f"FAIL: {f}")
        return 1

    print("AXIOM AUDIT PASSED: trust base is standard foundations + native_decide only.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
