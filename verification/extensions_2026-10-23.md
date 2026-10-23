# Effective dynamics and cluster extension scope

These sources consolidate six standalone supplements into the existing pinned library. They import Mathlib and are imported by Entropic.lean, so scripts/AxiomAudit.lean checks their theorem dependencies by originating module. No replacement of existing proofs or weakening of assumptions is intended.

| Module | Explicit theorem declarations | Scope |
| --- | ---: | --- |
| EmpiricalCertificates | 7 | Conditional expansion, acceleration intervals, equation-of-state sign and abundance identities |
| MuseProjection | 4 | Rational square-root brackets and finite weighted interval bounds; not a completed real-data regression |
| ConnectedClosure | 42 | Selected depletion action, positive current, local characteristic bounds, lag comparison and noise-delay algebra |
| EffectiveContact | 36 | Finite-work balance, admissible contact, warm enthalpy gates and sound-speed bounds |
| MergerContact | 8 | Central-pair momentum/angular-momentum and energy accounting |
| ClusterOutliers | 22 | Conditional gas balance, pressure/inventory bounds and finite transport conservation |

The original projects in the Sol and Fable workspace are, respectively: Unified empirical program 2026-10-23; Connected theory closure 2026-10-23; Effective dynamics and coupling 2026-10-23; Conservative cluster merger 2026-10-23; and Cluster outlier closure 2026-10-23. Original files and all saved numerical runs are preserved there. The publication integration record records source SHA-256 hashes and exact paper snapshots.

All six integrated source files now pass standalone Lean/mathlib 4.19 compilation and axiom checks. The original MuseProjection file was an unfinished numerical proof attempt; its three finite rational certificates are completed here using `decide +kernel`, without changing their statements. Its generic weighted-interval lemma is unchanged. This repository pins 4.35: successful CI, including the axiom audit, is the compatibility check. The upstream ledger totals and manuscript hash retain their original snapshot meaning; these additions do not silently reclassify its empirical claims.

## What is not certified

The modules do not certify FITS inputs, observational likelihoods, nonlinear simulations, the empirical MUSE selection, or the physical selection of the constitutive function, floor, target distribution or contact rate. The pressure and transport statements have explicit hypotheses. A positive transport inventory is not a dynamically selected cluster solution. The conserved particle merger is an effective realization and does not evolve the full depleted scalar stress. The minimal Einstein tensor action remains conditional on its physical matching.

## Verification

Run the repository's normal `lake build`, source scan, and `lake env lean scripts/AxiomAudit.lean`. The axiom audit enumerates theorem declarations by module, including these six modules, and permits only propext, Classical.choice and Quot.sound. The declaration count 119 excludes generated helper constants and is not an aggregate audited theorem count.
