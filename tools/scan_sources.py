#!/usr/bin/env python3
"""Fail if any Lean source under Entropic/ uses sorry, admit, native_decide or declares an axiom.

Comments and docstrings are removed first, so prose that mentions these words is ignored.
The axiom audit (scripts/AxiomAudit.lean) is the decisive check; this scan is a fast pre-check."""
from pathlib import Path
import re, sys

root = Path(__file__).resolve().parents[1]

def strip(text: str) -> str:
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); i = n if j < 0 else j; continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(text[i]); i += 1
    return "".join(out)

bad = []
for p in sorted((root / "Entropic").rglob("*.lean")):
    code = strip(p.read_text())
    for pat in (r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"(^|\n)\s*axiom\s"):
        if re.search(pat, code):
            bad.append(f"{p.relative_to(root)}: {pat}")
if bad:
    print("\n".join(bad)); sys.exit(1)
print("source scan passed: no sorry, admit, native_decide or axiom declarations")
