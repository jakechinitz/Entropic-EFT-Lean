# Papers

Current versions of the four papers, synced from the author's publication set on 2026-11-08. Earlier versions are archived with the author's Zenodo records, not here.

| Folder | Paper | PDF | SHA-256 (PDF) |
|---|---|---|---|
| [`full/`](full) | Entropic Scalar EFT: From Entanglement Microstructure to Gravity and Cosmic Structure | [Entropic_Scalar_EFT.pdf](full/Entropic_Scalar_EFT.pdf) | `5265d165a34107d3…` |
| [`compact/`](compact) | Entropic Scalar EFT: Microstructure, Gravity, and the Retained Quantum Sector (Compact Derivation) | [Entropic_Scalar_EFT_Compact.pdf](compact/Entropic_Scalar_EFT_Compact.pdf) | `c15f68f7706aad03…` |
| [`empirical-results/`](empirical-results) | History-dependent gravity and cosmological release: galaxy, cluster, and cosmological tests | [Empirical_Results.pdf](empirical-results/Empirical_Results.pdf) | `f06a5f1242c5e801…` |
| [`microstructure-cdt/`](microstructure-cdt) | A microscopic realization of causal triangulations with native matter and clock dynamics | [Microstructure_CDT.pdf](microstructure-cdt/Microstructure_CDT.pdf) | `cd388b1cb4fcd9d5…` |

## Contents

**full/**: The full theory paper; the canonical reference. The Lean ledger maps its 1,437 statements to Lean names. Source: `source/Entropic Scalar EFT.tex` (single file).

**compact/**: A condensed derivation of the full paper. Source: `source/Astra Quantum gravity completion compact.tex` (single file).

**empirical-results/**: The fifteen registered test families with their evidence and limits. Its data are in [`../data/`](../data). Source: `source/Empirical_Results.tex` with chapter inputs `01_` to `07_` and `figures/`.

**microstructure-cdt/**: The CDT construction and its registered finite tests. Simulation code and runs: [jakechinitz/cdt-microstructure](https://github.com/jakechinitz/cdt-microstructure). Source: `source/MICROSTRUCTURE_CDT.tex` with `chapters/`.

## Building a PDF

Each source folder compiles with `pdflatex` run twice from inside that folder (`latexmk -pdf` also works). The empirical paper needs its `figures/`; the CDT paper needs its `chapters/`.

## Papers and the Lean

The Lean formalizes the mathematical statements of the full paper. [`../ledger/LEDGER.md`](../ledger/LEDGER.md) lists every statement with its kind (exact, numerical, premise-conditional, data, interpretive), its status and the Lean names that prove it. Section and appendix numbers in the ledger refer to the full paper.

## Updating

`tools/sync_papers.py` copies the current set from the author's workspace (see its docstring). Full SHA-256 values of every file are in [`MANIFEST.json`](MANIFEST.json).
