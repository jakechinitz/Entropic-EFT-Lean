EMPIRICAL RESULTS: HISTORY-DEPENDENT GRAVITY AND COSMOLOGICAL RELEASE
Current edition: November 8, 2026, three-theory comparison with Pareto review.

CONTENTS
Empirical_Results.tex and its numbered inputs are the current manuscript.
Empirical_Results.pdf is the publication PDF. figures/ contains all supplied
figures, including the older LMC figure and the expanded current comparison.
Empirical_Results_Source.zip packages this edition's sources, PDF, figures,
verification scripts and saved comparison evidence. manifest.json hashes its
members. current_verification.json describes the current checks.

SAVED-RESULT VERIFICATION
From this directory, with Python 3:
  python audit_saved_results.py
This checks saved numerical scores, information-criterion arithmetic, the fifteen
test families, citations, cross-references and figure/input files. It runs no new
optimization, scientific simulation or Lean build.

FIGURE REPRODUCTION
With NumPy and Matplotlib installed:
  python figures/make_comparison_figures.py --output-dir figure_check
This regenerates the eight comparison figures from supplied saved results and
the explicitly stated benchmark formulas. --data-root can select another copy
of the three-theory evidence. The default input is evidence/three_theory.
The redshift illustration uses the matter-plus-constant-vacuum formula stated
in its caption; it is not an integrated release-history likelihood result.

BUILD
From the Sol and Fable workspace:
  python .organization/build_pdfs.py --paper empirical
  python .organization/publication_set.py check
The helper preserves the prior PDF and keeps compiler files in 05 Build Files.
For a standalone copy, run pdflatex on Empirical_Results.tex until references
settle (normally two or three passes). The supplied figures require no Python.

EVIDENCE AND REPRODUCIBILITY SCOPE
evidence/three_theory contains exact copies of the saved X1-X3 output files and
their original research scripts, plus the paired C6/C8 headline cosmology
results. evidence/source_manifest.json records their workspace origins and
SHA-256 hashes. The original research scripts retain their container paths;
RESULTS.md documents the path mapping. Rerunning those fits requires the source
workspace and its raw data and dependencies. The portable audit and plotting
commands above use the saved outputs without those external dependencies.
Original simulations and full observational data archives are not redistributed.

HISTORICAL REVIEW TOOLS
reproduce_review.py and refresh_verified_results.py reproduce the earlier
finite-ensemble, galaxy and release review using the workspace named by
--workspace. Use a separate extracted working copy: these scripts refresh
historical figures and verification files. Their October 23 reports, manifest
and the previous README are preserved under evidence/legacy_review.
They do not certify the later three-theory comparisons. Proof scopes and pinned
source snapshots are stated in the manuscript's provenance appendix.

PRESERVATION AND REVIEW
The pre-comparison sources remain in Previous PDFs/20261108_pre_three_theory_sources.
The exact inputs to this review, including the former source ZIP, remain in
Previous PDFs/20261108_pre_pareto_review. No original file was deleted.
The review compares both the prior 47-page edition and the immediate 57-page
edition. All 70 older displayed equation environments, all 15 test families,
and all 46 older references are retained. New comparison figures and four
references are included. The right panel of the LMC comparison retains the
three interpolation-function flux tests from the older figure.
The review record is in 04 Notes and References/Manuscript Reviews/Empirical
Pareto review 2026-11-08 in the source workspace.
