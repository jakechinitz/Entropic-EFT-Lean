EMPIRICAL RESULTS: HISTORY-DEPENDENT GRAVITY AND COSMOLOGICAL RELEASE
23 October 2026 - current 41-page edition

CONTENTS
Empirical_Results.tex and numbered TeX inputs: editable manuscript, including
05b_clusters.tex and 05c_cross_sector.tex. figures/ contains supplied figures.
Empirical_Results_Source.zip includes current sources, figures, records and PDF.
numerical_review.json preserves the original benchmark; current_verification.json
identifies the current exponential-allocation fit and imported research results.
manifest.json hashes the current package files. No previous PDF is discarded.

BUILD
From the Sol and Fable workspace:
  python .organization/build_pdfs.py --paper empirical
  python .organization/publication_set.py check
The helper preserves PDFs and keeps compiler files under 05 Build Files/PDF builds.
For standalone typesetting, compile Empirical_Results.tex with pdfLaTeX twice in
the supplied source directory; supplied figures require no simulation or Python.

REPRODUCTION
  python refresh_verified_results.py --workspace "C:/PATH/TO/Sol and Fable"
This imports the saved exponential-allocation fit, updates the redshift arithmetic
and figures, and preserves prior outputs. --legacy-linear selects the historical
linear-depletion benchmark. NumPy, SciPy and Matplotlib are required.

reproduce_review.py reproduces the original finite-ensemble, LMC, dwarf and release
review, then invokes the current supplement. It requires the source workspace
named in the provenance appendix. Original simulations and data archives are not
redistributed here. Neither script runs a new cosmological optimization or N-body
simulation. The current positive-allocation fit has chi-square 2227.8006205 versus
2228.3158253 for the matched LCDM pipeline; its approximations remain explicit.

PROOFS AND SCOPE
Six integrated modules add 119 explicit theorem declarations. The full pinned
Lean 4.35.0 build, source scan, axiom audit and citation check passed at
a6552daf39daf83d5159fcbcda698d1801731d24. Review branch:
https://github.com/jakechinitz/Entropic-EFT-Lean/pull/4
This is not a merge into the default branch. Proven conservation, positivity and
conditional inventory identities do not certify observed cluster fits, numerical
simulations, or the physical selection of the constitutive/contact laws.

VALIDATION
Both publication PDFs were compiled with resolved cross-references and citations.
All empirical pages and the changed main-paper pages were rendered and inspected;
all pages were checked for text outside the page. The supplied writing guide was
used for the integration. The dated T5 record includes source hashes, exact diffs,
proof logs and PDF review. Original source bytes and prior artifacts are preserved.
