CURRENT EDITION: 24 October 2026 (clusters edition)
This edition adds Section 3.7 (stock selection reaches the response law, with run
table and figure), Section 6.6 (stock selection discriminants), Section 9.3 (why
clusters remain fair samples: X-COP support radii and cell energies, contact runs
under four rules, X-ray elliptical check), source keys G8-G11 and eight references.
The sources it replaced are in Previous PDFs/20261024_pre_clusters_promotion_sources.
Records: 02 Research/Clusters edition 2026-10-24 and Cluster switch derivation
2026-10-24. The notes below describe the earlier edition and its reproduction
tools, which still apply to the unchanged chapters.

EMPIRICAL RESULTS: HISTORY-DEPENDENT GRAVITY AND COSMOLOGICAL RELEASE
23 October 2026 - current 38-page edition

CONTENTS
Empirical_Results.tex and numbered TeX inputs: editable manuscript, including
05b_clusters.tex, 05c_cross_sector.tex and 05d_distinctive.tex.
figures/ contains supplied figures.
Empirical_Results_Source.zip includes current sources, figures, records and PDF.
numerical_review.json preserves the original benchmark; current_verification.json
identifies the current exponential-allocation fit and imported research results.
manifest.json hashes the current package files. No previous PDF is discarded.

ORGANIZATION
Table 1 covers all fifteen registered test families and links to each discussion.
Part I: Distinctive predictions and discriminating tests.
Part II: Recovery of established phenomenology.
The status of each test is stated separately; coverage does not mean all tests
passed. The T6 record documents this editorial organization and PDF review.

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

The earlier T6 edit reorganizes existing evidence without rerunning simulations,
likelihood fits or Lean proofs. All 42 pages of that edition were rendered and checked;
all fifteen overview entries and their section links are present and resolved.

CURRENT FORMATTING
The current 38-page edition uses the main paper's A4 one-inch page geometry,
Computer Modern text and mathematics, black article headings, centered title,
and continuous plain page numbering. All seven figures and fifteen test families
are retained. Formatting records are in 02 Research/Publication formatting
alignment 2026-10-23. The current source bundle reproduces this edition.

28 OCTOBER 2026 UPDATE
05_cosmology (one-harness table, source C6), 02_acceleration (support-limited lensing,
source G12), 04_dwarfs (new subsection on which satellites keep their stock, source G12),
07_references (read19) and 06_interpretation_and_audit (keys G12, C6) were edited.
Previous sources: Previous PDFs/20261028_pre_tension_updates_sources. manifest.json and
current_verification.json were not regenerated for these edits.

28 OCTOBER 2026 (EVENING): 04_dwarfs gains one paragraph on the release-gate assignment (source G12).
Previous source: Previous PDFs/20261028b_pre_gate_sources.

2026-10-28 (c): Section 15 and Appendix N.8 restate the RAR cell as the horizon-thermal tilt mode with lever g_share,eff c/H; the RAR is derived given the tilt mode, its horizon thermalization, and the lever, whose coefficient is the one open number. See Previous PDFs/20261028c_pre_rar_sources/CHANGE_RECORD_20261028c.txt.

2026-10-29: consistency pass. a0 quoted at the theory's own fitted H0 (68.458; 1.250e-10) beside the Planck value; Section 18 descendant sentence; lever projection applied once; 27.3 stationary-occupation qualifier; release-integral gap; Lean inventory (222 modules, 5,038 theorems) and repository link; proofs zip and local library synced to GitHub main cfcfa373. See Previous PDFs/20261029_pre_consistency_sources/CHANGE_RECORD_20261029.txt.

2026-10-29 (b): Section 27.3 adds the Hubble constant from galaxy dynamics (a0 = eps c H0; SPARC absolute-distance galaxies give H0 = 66 +- 11; a 2% a0 separates 68.5 from 73); same in the compact and empirical papers. See Previous PDFs/20261029b_pre_h0_sources/CHANGE_RECORD_20261029b.txt.
