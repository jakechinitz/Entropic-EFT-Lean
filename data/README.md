# Data for the empirical results

Everything here supports the paper in [`../papers/empirical-results/`](../papers/empirical-results). The keys (G1, C8, D1, …) are the source keys of that paper's audit table (Section 9, "Sources").

| Folder | Contents |
|---|---|
| [`empirical/package/`](empirical/package) | The paper's reproduction package: `manifest.json` (hashes), `current_verification.json` and `numerical_review.json` (fits and benchmarks), `refresh_verified_results.py` and `reproduce_review.py` (scripts), and the package `README.txt` |
| [`empirical/sources/`](empirical/sources) | The research folders the audit table cites: notes, scripts, registered protocols and result files |
| [`empirical/sources_index.json`](empirical/sources_index.json) | Every included file, and every file left out with its size |
| [`../registered/`](../registered) | Registered predictions with SHA-256 files |
| [jakechinitz/cdt-microstructure](https://github.com/jakechinitz/cdt-microstructure) | CDT simulation engine, run protocols and replication data (separate repository) |

**What is included.** Text, code and small data files (at most 1 MB each: `.py .json .md .txt .csv .tex .yaml .toml .sh .npy .npz` and similar) from each cited folder.

**What is left out**, and listed in `sources_index.json`:
- run directories (`analysis_*`, `run_*`, `runs`, `logs`, `inputs`, `workspace`);
- vendored dependencies;
- copies of other repositories;
- Lean copies (the Lean lives at the repository root);
- large or binary outputs such as simulation snapshots, FITS images and PDFs.

Those stay in the author's archive.

## Source keys

| Key | Folder under `empirical/sources/` | What it supports |
|---|---|---|
| T2 | [`Spacetime consolidation 2026-10-16`](empirical/sources/Spacetime%20consolidation%202026-10-16) | Finite geometry, interaction, matter, and clock construction. |
| G2 | [`LMC and satellites checks`](empirical/sources/LMC%20and%20satellites%20checks) | External-field QUMOND surface-flux comparison. |
| G3 | [`Crater II and Antlia 2 vs LCDM`](empirical/sources/Crater%20II%20and%20Antlia%202%20vs%20LCDM) | Core observation likelihood, priors, and hash identity. |
| G4 | [`Crater II and Antlia 2 vs LCDM`](empirical/sources/Crater%20II%20and%20Antlia%202%20vs%20LCDM) | Current moving-LMC trajectories and evidence. |
| G6 | [`Crater II and Antlia 2 vs LCDM`](empirical/sources/Crater%20II%20and%20Antlia%202%20vs%20LCDM) | Model-error sensitivity and approximate observational mocks. |
| G7 | [`Stock adjustment resolution 2026-10-21`](empirical/sources/Stock%20adjustment%20resolution%202026-10-21), [`Halo replication audit 2026-10-21`](empirical/sources/Halo%20replication%20audit%202026-10-21) | Radial adjustment, retained angular marginals, and fixed-target halo tests. |
| G8 | [`Galaxy sector resolution 2026-10-24`](empirical/sources/Galaxy%20sector%20resolution%202026-10-24) | Selection constraints, exact constrained minimiser, three-dimensional contact runs, lensing bound, and independent audits. |
| G9 | [`Contact rule physical basis 2026-10-24`](empirical/sources/Contact%20rule%20physical%20basis%202026-10-24) | Bose relative-entropy bias, equipartition weight, zero-temperature detailed balance, Bose-functional runs, and the Lean module . |
| G10 | [`Bose contact observed clusters 2026-10-24`](empirical/sources/Bose%20contact%20observed%20clusters%202026-10-24) | Forty contact runs on seven X-COP clusters without a cluster gate, at galaxy-scaled and fixed work allowances, with numerical audit. |
| G11 | [`Cluster switch derivation 2026-10-24`](empirical/sources/Cluster%20switch%20derivation%202026-10-24) | Record-dominated supports and cell energies of the X-COP clusters, the cell reservoir E_{cell}/M_{stock}to V_f^2, contact runs under four rules, and gated galax |
| G12 | [`Highest-leverage tensions 2026-10-28`](empirical/sources/Highest-leverage%20tensions%202026-10-28) | Isolated-lens population forward model with support-limited stock, and the satellite support assignment for the classical dwarfs, with independent review. |
| C1 | [`Full Planck tied abundance`](empirical/sources/Full%20Planck%20tied%20abundance), [`Dark energy prediction tests`](empirical/sources/Dark%20energy%20prediction%20tests) | Matched likelihood, data handling, Boltzmann mapping, and reference ΛCDM result. |
| C2 | [`Release zoom`](empirical/sources/Release%20zoom) | Archived PPF release fit, reference history, and hydrodynamic mixing test. |
| C7 | [`Dark energy normalization 2026-10-30`](empirical/sources/Dark%20energy%20normalization%202026-10-30) | Retention gate from the cooling criterion and from the archived run, and the release integral, h and Omega_Lambda against the gate. |
| C8 | [`Retention gate from feedback simulations 2026-10-31`](empirical/sources/Retention%20gate%20from%20feedback%20simulations%202026-10-31) | Release integral with the feedback-resolved occupation as the retention gate, and its uncertainty; holds the frozen-history fits. |
| C3 | [`Formation operator check`](empirical/sources/Formation%20operator%20check) | Formation abundance and the 5.333 mass convention. |
| C4 | [`High leverage closure 2026-10-21`](empirical/sources/High%20leverage%20closure%202026-10-21) | Direct clock-fluid implementation, matched linear-lensing fits, and numerical checks. |
| T5 | [`Manuscript cluster and dynamics integration 2026-10-23`](empirical/sources/Manuscript%20cluster%20and%20dynamics%20integration%202026-10-23) | Preserved source hashes, integration diffs, six-module manifest, compilation checks and PDF validation. The six modules are included in the checked extension sn |
| T6 | [`Empirical fifteen-test structure 2026-10-23`](empirical/sources/Empirical%20fifteen-test%20structure%202026-10-23) | Fifteen-family coverage map, preserved source versions, editorial diffs, and validation of the two-part presentation. |
| U1 | [`Unified empirical program 2026-10-23`](empirical/sources/Unified%20empirical%20program%202026-10-23) | Fifteen-sector evidence register; S01–S15 identify the selected datasets, saved results, source URLs, and remaining tests. |
| C5 | [`Unified empirical program 2026-10-23`](empirical/sources/Unified%20empirical%20program%202026-10-23) | Exponential-allocation fit, matched reference, and saved observables. |
| C6 | [`Highest-leverage tensions 2026-10-28`](empirical/sources/Highest-leverage%20tensions%202026-10-28) | One-harness ΛCDM and direct geodesic release fits across supernova, neutrino and lensing settings, with independent review. |
| D1 | [`Connected theory closure 2026-10-23`](empirical/sources/Connected%20theory%20closure%202026-10-23) | Depletion action, unchanged linear domain, lag and noise bounds, and conditional tensor calculation; 42 Lean declarations. |
| D2 | [`Effective dynamics and coupling 2026-10-23`](empirical/sources/Effective%20dynamics%20and%20coupling%202026-10-23) | Finite-work contact, warm fluid stress, compression and feedback checks; 36 Lean declarations. |

## Reproducing

The scripts expect the author's workspace layout. Most read their inputs relative to their own folder, and those in `package/` take `--workspace PATH`. Results quoted in the paper match the JSON outputs in the corresponding folder.
