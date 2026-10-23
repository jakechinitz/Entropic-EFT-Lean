# Formalization plan (v4.35.0)

Project: `Entropic` (our modules, 225 theorems) + `EntropicEFT` (GitHub v0.8.0 library,
193 theorems, ported unchanged to Lean/Mathlib v4.35.0). One lake project.

Ledger: 1,437 claims from the manuscript (C01–C15 files, merged in LEDGER.md).
  A 891 (easy 550 / medium 220 / hard 117), B 209, C 217, D 69, E 46.
Targets: A and B are proved outright. C claims are proved with the premise written as an
explicit definition of the model (not an empty `Prop` label). D are recorded as numeric
comparisons with the cited data. E are not formalized.

Old-library policy:
  * its 193 theorems are kept and cross-linked;
  * typed "...Math" certificates (GibbsAnalysis, EtaUniquenessMath, MultiplicativeLapseMath,
    FiniteEntropyFacts, GaussianDeterminantMath, ReplacementChannelMath, ...) are discharged
    by proofs and instantiated;
  * all-`Prop` label structures (42 + 9 "Math" labels) are retired: they state nothing.
  * native_decide replaced by decide where the kernel can carry it.

Chunks (one module group per chunk, each ends with build + axiom audit + ledger update):
  1  setup: port to v4.35, ledger, plan                          DONE
  2  App. B + Sec. 5-9   (C04, part of C01): closure ensemble, branch audits, B.5 tables,
     discharge GibbsAnalysis / EtaStarSpec / UniqueEtaStarCertificate        DONE
     (also: EtaUniquenessMath, NumericalSpineCertificate instantiated; all 30 native_decide
      in EntropicEFT replaced by kernel decide or proofs; audit 0 nonstandard axioms)
  3  App. C, D, E        (C05 + weak-field part of C01)                        DONE
  4  App. F, G           (C06) + Sec. 21-22 (part of C03)                      DONE
  5  App. H.1-H.9a       (C07)                                               DONE
     (AppH1.Algebra/Marked/Kinematics: 78 of 127 C07 items proved or mapped to existing, 3 partial;
      rest deferred rep theory / simulations / data / premise-C; audit 750 + 727, 0 nonstandard)
  6  App. H.10           (C08)                                               DONE
     (AppH10 Gaussian/Legendre/Elimination/Pullback/Spectral/Symbols: finite-regulator Gaussian
      determinant theorem proved from Lebesgue measure; audit 851 + 727, 0 nonstandard)
  7  App. H.11-H.15      (C09)                                               DONE
     (AppH11 Records/Polar/Clock/Frame: records, Kraus, lifts, carrier isometry, polar generator,
      Fubini-Study, bridge non-additivity, covariance, Dirac-Kahler, coarse symbol)
  8  App. I, J           (C10)                                               DONE
     (AppIJ Shells/Color/Cdt: closure solvability by IVT, Fisher=Var, Kac, entropy bound, q^{N^2}
      Gaussian ladder, route/Gram/Kraus/t8 algebra, diamond girth, thermodynamic integration, Newton limit)
  9  App. K-N            (C11, C12)                                          DONE
     (AppKN Scalars/Response/Fields: windows, lag, plateau, capacity equations, first law, carriers,
      rank-one Hessians, occupation, two-pole response, Misner-Sharp, saddle-splay, cycle invariants)
 10  App. O              (C13)                                               DONE
     (AppO Release/Flow/Numerics: unimodular algebra, release positivity by integrating factor,
      contact ratio and s<=3, projection bounds, entropy dissipation, mixing fraction, isometries,
      certified uniform-core root, BSC, recurrence margin, formation energy)
 11  App. P              (C14)                                               DONE
     (AppP Records/Expansion/Numbers/Spin: recovery map, renewal kernel, conditioned-law identities,
      Jensen, data processing, second-order MI and FS expansions with remainders, spin-3/2 ladder
      spectra and bridge traces, Niven irrationality of the gluing angle, certified angles)
 12  App. Q              (C15)                                               DONE
     (AppQ Algebra/Fock/Weights: frame covariance and exp-conjugation invariance, transfer projector,
      potential minimum, hinge kernels, channel-area chain, bond Hamiltonian, tridiagonal count form,
      fusion coisometry, polar gluing, spin-1 pair, weight counts)
 13  Main text Parts IV-VIII remainder (C02, C03)                     DONE
     (Main Galactic/Core/Cosmo: carrier projectors, Bose cell, Q_perp integral and derivative, cap
      radius, source inversion, telegrapher poles, release/vacuum exchange; C01 remainder; Kirchhoff,
      free-energy centering, CDT couplings, Gaussian KL, no-signaling, native units)
 14  final: deferred sweep, citations, retirement map, CLAIMS map, manuscript R.1 text, global audit   DONE
     (Sweep Spin/Algebra/Analysis/Counting/Staggered/Dirac/Information/Gaussian/Legacy + RetainedRelaxation:
      spin-3/2 projectors, positivity and transfer semigroup, leakage sum, 3D Gaussian and first moment,
      two-pole transform and sum rule, S₇ orbit count, staggered complex identities, Dirac frame flips,
      fused-label cap, Hermite Gram, legacy instances; CiteCheck 0 unresolved; see CLAIMS.md, RETIREMENT.md;
      the v0.8 library is merged into the single library as Entropic.EFT, namespace EntropicEFT → Entropic.EFT)

Second pass on the 196 open claims (see OPEN_TRIAGE.md for groups, importance, tractability).
Each chunk: attempt every target in its groups; time-box anything that resists after real prodding
and record the reason in the ledger; build; axiom audit; CiteCheck; ledger + PLAN (mark DONE);
deploy with originals preserved; push to the PR branch lean435-single-library; short report.
 15  G1 Schur lemma for ladder irreps of every spin, commutants, equivariant uniqueness; duplicate sweep   DONE
     (Pass2 Schur/Pair/PairGen/RealForms/SU3Form/Intertwiner/DiagCommutant: 10 proved, 2 partial;
      C04-51, C15-13, C14-80, C09-31 time-boxed with reasons)
 16  G3 first-variation theorem with compact support on R^n; Euler-Lagrange equations of the actions   DONE
     (Pass2 Var/Fields/IBPForm/Harmonic: 6 proved incl. C11-56, C03-133 brought forward from chunk 17; 5 partial;
      11 time-boxed with reasons)
 17  G4 coordinate GR: conformally flat curvature, weak-field reduction, maximum principle and Phi = Psi, static spherical reduction   DONE
     (Pass2 Conformal/ADM, Harmonic: C11-50, C11-51, C11-52 proved, C01-44 partial (compact support);
      C11-56, C03-133 proved in chunk 16; warped-product, Lorentzian and Regge items time-boxed with reasons)
 18  G5, G6, G9 matrix calculus and ODE, finite combinatorics, special-function and stated-input numerics   DONE
     (Pass2 Kinetic: C15-30 proved, C15-43 partial; the rest need matrix-function calculus, Haar measure,
      quantum entropy, matrix-tree, Γ enclosures or encoded data that Mathlib lacks; reasons in the ledger)
 19  G2, G7, G8 top multiplet and coherent states, Lie closure, ensemble numerics at eta_*
 20  G12 reclassification, final audit, CLAIMS/RETIREMENT/README/drop-in refresh, deploy, PR update
