#!/usr/bin/env python3
"""Check the axiom footprint emitted by `Scripts/AxiomAudit.lean`.

Usage:
    lake env lean Scripts/AxiomAudit.lean > axiom-footprint.txt
    python tools/check_axioms.py axiom-footprint.txt

Fails (exit 1) if any audited theorem depends on an axiom outside the declared
trust base, or if the audit produced no output at all (which would silently turn
this check into a no-op).

The trust base has exactly two parts.

1. Standard foundations: `propext`, `Classical.choice`, `Quot.sound`.

2. Enumerated `native_decide` certificates. Lean 4.33 does not discharge
   `native_decide` through one global `Lean.ofReduceBool`; each use mints its own
   opaque axiom named after the declaration that used it, e.g.

       EntropicEFT.UV.boundaryStates_card._native.native_decide.ax_1_1

   That is what makes "enumerated" a literal claim rather than a figure of
   speech: every appeal to compiled evaluation is individually named, and this
   script pins the exact set of declarations allowed to make one. A new
   `native_decide` anywhere in the audited dependency cone introduces a name that
   is not in EXPECTED_NATIVE_SOURCES and fails the build, so the certificate list
   cannot grow silently.

`sorryAx` — what a `sorry` introduces — is in neither category, so a `sorry`
anywhere beneath an audited theorem fails this check.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

FOUNDATIONS = {
    "propext",
    "Classical.choice",
    "Quot.sound",
}

# A per-declaration native_decide certificate, e.g.
# "EntropicEFT.UV.boundaryStates_card._native.native_decide.ax_1_1".
NATIVE_AX = re.compile(r"^(?P<source>.+)\._native\.native_decide\.ax_\d+_\d+$")

# Older/alternative form: the single global compiled-evaluation axiom.
LEGACY_NATIVE = "Lean.ofReduceBool"

# The complete set of declarations permitted to appeal to compiled evaluation
# within the audited dependency cone. All are finite enumerations over the
# boundary ensemble or its subset/spectrum bookkeeping. Adding a name here is a
# deliberate widening of the trust base and should be argued for in BUILD_STATUS.md.
EXPECTED_NATIVE_SOURCES = {
    "EntropicEFT.UV.allPortAssignments_card",
    "EntropicEFT.UV.boundaryStates_card",
    "EntropicEFT.UV.spectrum_max",
    "EntropicEFT.UV.spectrum_min",
    "EntropicEFT.UV.unorientedStates_card",
    "EntropicEFT.Structure.four_subsets_share",
    "EntropicEFT.Structure.johnson_fibration",
    "EntropicEFT.Structure.support_card_four",
    "EntropicEFT.Structure.unweighted_mean_exact",
}

# "'Foo.bar' depends on axioms: [propext, Classical.choice, Quot.sound]"
DEPENDS = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.S)
# "'Foo.bar' does not depend on any axioms"
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")


def classify(axiom: str) -> tuple[str, str | None]:
    """Return (kind, native_source) for an axiom name."""
    if axiom in FOUNDATIONS:
        return "foundation", None
    if axiom == LEGACY_NATIVE:
        return "native", LEGACY_NATIVE
    m = NATIVE_AX.match(axiom)
    if m:
        return "native", m.group("source")
    return "disallowed", None


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: check_axioms.py <axiom-footprint.txt>", file=sys.stderr)
        return 2

    text = Path(argv[1]).read_text()

    audited: list[tuple[str, set[str]]] = []
    for m in NO_AXIOMS.finditer(text):
        audited.append((m.group(1), set()))
    for m in DEPENDS.finditer(text):
        axioms = {a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()}
        audited.append((m.group(1), axioms))

    if not audited:
        print("FAIL: no `#print axioms` output found — the audit did not run.")
        print("----- captured output -----")
        print(text)
        return 1

    failures: list[str] = []
    certificates: set[str] = set()
    native_sources: set[str] = set()

    for name, axioms in sorted(audited):
        foundations, natives, disallowed = set(), set(), set()
        for ax in axioms:
            kind, source = classify(ax)
            if kind == "foundation":
                foundations.add(ax)
            elif kind == "native":
                natives.add(ax)
                certificates.add(ax)
                if source is not None:
                    native_sources.add(source)
            else:
                disallowed.add(ax)

        if disallowed:
            failures.append(
                f"{name} depends on disallowed axiom(s): {', '.join(sorted(disallowed))}"
            )
            status = "FAIL"
        elif natives:
            status = "OK  "
        else:
            status = "OK  "

        rendered = ", ".join(sorted(foundations)) if foundations else "(no foundations)"
        if natives:
            short = sorted({n.rsplit("._native.native_decide.", 1)[0] for n in natives})
            rendered += "  + native_decide: " + ", ".join(short)
        if disallowed:
            rendered += "  + DISALLOWED: " + ", ".join(sorted(disallowed))
        print(f"{status} {name}: {rendered}")

    print()
    print(f"audited {len(audited)} declarations")

    unexpected = native_sources - EXPECTED_NATIVE_SOURCES - {LEGACY_NATIVE}
    missing = EXPECTED_NATIVE_SOURCES - native_sources

    print(
        f"native_decide certificates in the audited cone: {len(certificates)} "
        f"across {len(native_sources)} declarations"
    )
    for source in sorted(native_sources):
        note = "" if source in EXPECTED_NATIVE_SOURCES or source == LEGACY_NATIVE else "  <-- UNEXPECTED"
        print(f"  - {source}{note}")

    if missing:
        # Not a failure: a certificate disappearing means a proof stopped relying on
        # compiled evaluation, which is a strict improvement. Report it so the
        # expected set can be tightened.
        print()
        print("NOTE: expected native_decide sources no longer appear (trust base shrank):")
        for source in sorted(missing):
            print(f"  - {source}")
        print("Consider removing these from EXPECTED_NATIVE_SOURCES.")

    if unexpected:
        failures.append(
            "new native_decide certificate(s) not in EXPECTED_NATIVE_SOURCES: "
            + ", ".join(sorted(unexpected))
        )

    if failures:
        print()
        for f in failures:
            print(f"FAIL: {f}")
        return 1

    print()
    print(
        "AXIOM AUDIT PASSED: standard foundations plus the enumerated "
        "native_decide certificates only."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
