# Formation operator: the open list

Date: 2026-10-03. Sources: "Opus carrier completion.tex" (H.7, J.9, O.2, O.3, O.7, O.9, O.11, O.13, P.7a, §15 carrier rules). Scripts: `formation_check.py`, `stress_transfer_check.py`, with outputs in the matching `_output.txt` files.

## Summary

| Item | Result | Grade |
|---|---|---|
| 1. Space-filling clock sector | The only space-filling phase in the manuscript is the condensate common phase of H.7. It orders at the substrate scale, so the clock already exists before Σ₀. A clock-absence gate cannot work; the gate is the source-label ledger, which needs no space-filling carrier. | Identified; gate replaced |
| 2. Onset temperature ξ | No electron-scale ordering transition exists in that sector: restoring it at m_e needs λ/Z ≈ 10⁴². The second-law floor kT ≥ m_ec²/ln 2 proposed in the first pass does not survive the second pass (see §2). Formation fires on the first labelable conserved charge, between sphaleron freeze-out and the QCD crossover, and the vertex weight bound (§6) makes it effectively instantaneous. | ξ not an independent number; floor withdrawn |
| 3. Absorbing lock | Isometry and forward-only export do not by themselves forbid unlocking. What is absorbing is the label ledger: the density of unlabelled conserved charge, n_∅ = 0, is preserved by every written operation, at any temperature below the sphaleron scale. | Theorem for the written transfer plus one explicit ledger rule |
| 4. Source is conserved charge | A Lagrangian cap fixed on Σ₀ is defined only for the content of a conserved current. Thermal pairs carry zero net charge, so they source nothing. | Derived from the Lagrangian-cap definition |
| 5. Plasma pays ρ_b/ε | The exchange current conserves energy and gives a radiation deficit equal to ρ_b/(ερ_r) at Σ₀, between 4×10⁻¹² and 8×10⁻⁷ over the allowed window. Λ cannot pay (O.2 with Law III). | Verified numerically |
| 6. Vertex weight | Cap filling before fitted modes enter the horizon needs a per-tick weight above e^{−16.1g}; one or two joint recurrences pass, three fail. | Derived |
| 7. Formation isometry | Explicit mirror of the O.13 release isometry; ledger absorption checked by full enumeration on a finite model. | Verified on the model |
| 8. Tied abundance | Compressed priors: the tied model beats ΛCDM by about 2. Full Planck high-ℓ with the released share's lensing deficit: it matches ΛCDM (2226.90 vs 2226.77) with one fewer parameter, and the data put the ratio at 5.326. ACT DR6 + Planck PR4 lensing reconstruction does not separate the models (Δχ² = 0.5). | Tested on the full high-ℓ likelihood and lensing |

## 1. The space-filling sector

H.7 writes the candidate condensate as σ₀ = √n̄ e^{iθ₀} v. Its common phase is massless when number U(1) is exact, and a background relational phase current ∂_χθ₀ ≠ 0 makes it a clock. Three facts follow.

- **Noether correspondence.** S_comm is shift-symmetric in φ, and its Noether current λ∇^μφ is the committed density current. Identifying φ with the condensate common phase maps shift symmetry onto number U(1) and committed density onto U(1) charge. In S_CΛ the only explicit breaking is V_F(φ), and microscopically that is the marked drain, which Law III makes one-signed. So the committed charge changes only through the drain after Σ₀. This is the Noether form of no-late-recruitment.
- **The clock predates Σ₀.** The condensate's chemical potential is ε₀ ~ E_* = ħ/τ_* = 1.22×10¹⁹ GeV. Its phase therefore orders, and starts rotating, at the substrate scale, long before any baryon exists. A gate of the form "no clock here" is never satisfied after that epoch. It would fire once at the Planck epoch, when ρ_b = 0, and form nothing.
- **The stock is not space-filling.** With c_s = 0, committed charge stays where it is injected. At Σ₀ baryons occupy between 10⁻⁷⁶ (second-law floor) and 10⁻⁶⁰ (sphaleron freeze-out) of primitive cells, so a charge-absence gate evaluated cell by cell would re-arm almost everywhere.

**Consequence.** The gate has to sit on conserved charge, not on the clock or the stock (item 3). That gate needs no space-filling carrier, because newly created matter carries no net conserved charge.

## 2. Onset temperature

**Ordering transition (negative result).** For the H.7 action, the O(2N) thermal mass gives T_c² = 12Zμ²/[λ(N+1)].

| Light components | λ/Z = 1, μ = E_* | λ/Z needed for T_c = m_ec² |
|---|---|---|
| Common phase only (relative modes gapped) | T_c = 2.4 E_* | 3.4×10⁴⁵ |
| All 1680 components | T_c = 0.08 E_* | 4.1×10⁴² |

Coupling the condensate to the Standard Model plasma through gravitational-strength terms gives δm² ~ T⁴/E_*², which again puts T_c near E_*. No electron-scale sign change exists in this sector.

**Second-law floor (withdrawn on the second pass).** The first pass priced the stock at ε_rec = m_ec²/ln 2 = 0.737 MeV per nat and treated formation as a closed exchange between bath and stock. That gave ΔS_tot = Q(1/ε_rec − 1/kT) and a floor kT ≥ 0.737 MeV. Three things in the manuscript break the derivation (`pricing_and_vertex_check.py`).

1. **The record scale is not fixed.** The running law κ_m(ℓ) = ħ/(cℓ ln 2) gives a floor ħc/(ℓ ln 2), which spans 40 orders of magnitude over the candidate scales for the stock:

   | Record scale ℓ | Floor |
   |---|---|
   | Cell L_* | 1.8×10¹⁹ GeV |
   | Proton Compton | 1.35 GeV |
   | Proton charge radius | 339 MeV |
   | Electron Compton | 0.737 MeV |
   | 1 Å | 2.8 keV |
   | Hubble radius | 2×10⁻³⁹ MeV |

   The committed density is written as ρ = E₀n with n counted in committed cells, which points toward the cell scale, where the floor would forbid thermal formation altogether.

2. **The sign is ambiguous.** Mass–Entropy Equivalence reads mass as missing entanglement. If committed entropy is a deficit, a closed exchange changes total entropy by −Q/kT − Q/ε_rec, which is negative at every temperature.

3. **Formation is not closed.** J.9 routes formation through the marked defect vertex, and that vertex sits inside the renewal step, which exports g nats per refreshed cell per tick into history. At the QCD crossover this is 5×10⁶⁹ nats per baryon per tick, against a bath loss of 32 nats per baryon for the entire formation. The second law does not bind.

The floor, the "pre-BBN is derived" statement, and the link to the de Sitter suppression are withdrawn. Nothing else in this note depended on them. Pre-BBN formation follows instead from the ledger construction: formation acts on the first labelable conserved charge, and the vertex is fast (§6).

**Window for Σ₀.**

| Candidate Σ₀ | T | z₀ | ξ | Radiation debit |
|---|---|---|---|---|
| Sphaleron freeze-out | 131.7 GeV | 1.7×10¹⁵ | 2.6×10⁵ | 4.4×10⁻¹² |
| QCD crossover | 156.5 MeV | 1.1×10¹² | 306 | 3.7×10⁻⁹ |

Every cosmological mode is superhorizon at both epochs, so δ_c = δ_b follows.

## 3. What is absorbing

**Isometry is not enough.** An unlock branch |1⟩_s|0⟩_H → |0⟩_s|U⟩_H with U orthogonal to the other outputs is just as isometric as the lock. Forward-only export forbids re-importing a specific record. It does not forbid a new process that writes "unlocked" forward. So no thermal order parameter is absorbing for structural reasons.

**The absorbing quantity is the label ledger.** Let n_∅ be the density of conserved baryonic charge carried without any source label, fine or coarse. Then:

- **Formation** acts only on n_∅ and sets it to zero (item 4).
- **O.9** gives the local label operations as preserve, release and merge, with no strip operation.
- **Release (O.3)** leaves the metric-visible remainder associated with the retained coarse carrier Y. The carrier passes from fine label A to the coarse label of Y and is never unlabelled.
- **Descendants inherit** the parent's label. This is the carrier rule that the NGC 5291 tidal dwarfs select (χ² of 0.5 for inheritance against 48 for separate carriers).
- **Charge conservation.** Net baryon number and charge are conserved below sphaleron freeze-out (131.7 GeV). The defect Hamiltonian conserves n_m.

So after Σ₀, ∇_μ(n_∅u^μ) = 0 with n_∅ = 0, and nothing in the bulk raises it.

**Late environments.**

- **Hot environments.** Supernova cores (30–50 MeV), neutron-star mergers, GRB fireballs (~MeV), and heavy-ion collisions (≤ 0.5 GeV) all lie far below 131.7 GeV and contain only labelled charge. None of them re-fires formation.
- **Released gas in galaxies.** This is the case that matters for the dark-energy ledger, and it is blocked two independent ways:
  1. **Ledger:** the gas is coarse-labelled.
  2. **Energy:** a plasma payer needs 4.99 GeV per baryon, against at most ~1% of m_pc² of local thermal plus nuclear energy.

**Stock survival.** No operator in the written transfer converts stock into heat. The one-step vertex does not touch c_{A,c}. The release isometry exports into history, sending η* to Λ and the rest to R. The pinned stock is therefore protected the way a baryon is: by an exact conservation law (the shift/U(1) charge) whose only breaking channel is the one-signed drain.

**One rule must be written explicitly:** carrier loss moves a carrier from its fine label to the coarse label of the retained carrier, and the coarse label's cap equals its retained R.

## 4. The source is conserved charge

A Lagrangian label marks the flow lines of a conserved current. The content of a Lagrangian element, and therefore a cap M_A/ε fixed on Σ₀, is time-independent only if the density is conserved. Thermal pair number is not conserved:

| T (MeV) | Thermal e± per net charge | Annihilation rate / H | Pair lifetime |
|---|---|---|---|
| 0.737 | 4.6×10⁸ | 1.8×10¹⁷ | 1.5×10⁻¹⁷ s |
| 0.511 | 4.3×10⁸ | 1.1×10¹⁷ | 5×10⁻¹⁷ s |
| 0.030 | 3.0×10³ | 3×10¹⁰ | 1×10⁻⁷ s |
| 0.020 | 1.1 | 7×10⁶ | 9×10⁻⁴ s |

If pairs were counted at T = m_e, the stock would be 0.46 of the radiation density and 4×10⁵ times the baryonic cap. Annihilation would then release it into Λ and R. Weighting by net charge gives pairs exactly zero source, and the same weighting is what makes the cap Lagrangian.

The cap is fixed at the mass per baryon on Σ₀, which is 0.24% above today's value at the QCD crossover (before helium binding). The abundance prediction shifts from 5.321 to 5.333, against 5.364 ± 0.065: 0.47σ.

## 5. Stress transfer

The exchange current is:

- ∇_μT_c^{μν} = Q u^ν and ∇_μT_rad^{μν} = −Q u^ν;
- Q = (ρ_b/ε) u·∇s.

`stress_transfer_check.py` integrates this through a tanh lock of widths 0.05 and 0.3 in ln T:

| T₀ | ρ_c/(ρ_b/ε) final | Radiation deficit | ρ_b/(ερ_r) at T₀ | Energy residual |
|---|---|---|---|---|
| 156.5 MeV | 1.000000 | 3.7–3.8×10⁻⁹ | 3.70×10⁻⁹ | < 10⁻⁸ |
| 0.737 MeV (late test case) | 1.000000 | 7.9–8.1×10⁻⁷ | 7.85×10⁻⁷ | < 10⁻⁸ |

**Λ cannot pay.** By O.2, Λ changes only through the volume-singlet projection of the marked drain, which Law III makes one-signed (E_Λ is monotone). A formation step paid by V_F would need a negative drain. In S_CΛ language, formation is an exchange with radiation, not a step in V_F. S_CΛ therefore needs this one exchange coupling added, with support on the formation epoch.

## 6. Formation vertex weight

To keep δ_c = δ_b, the cap must fill (∫Γ_form dt ≥ 5.5) before the modes being fitted enter the horizon. Starting at the QCD crossover or at sphaleron freeze-out gives the same requirement:

| Deadline | Mean rate needed | Per-tick weight needed |
|---|---|---|
| Planck ℓ ≈ 2500 (z = 9.1×10⁴) | 1.9×10⁻⁹ s⁻¹ | e^{−16.1g} |
| Lyα k = 1 Mpc⁻¹ (z = 4.6×10⁵) | 4.9×10⁻⁸ s⁻¹ | e^{−15.7g} |
| BBN onset (T = 0.1 MeV) | 4.2×10⁻² s⁻¹ | e^{−13.9g} |

The manuscript's natural weights per tick compare as follows:

| Weight | Value | Rate (s⁻¹) | Against e^{−16.1g} |
|---|---|---|---|
| ζ_* | 5.1×10⁻³ | 10⁴¹ | passes |
| e^{−7g} (one marked recurrence) | 2.8×10⁻²³ | 5×10²⁰ | passes by 3×10²⁹ |
| e^{−14g} (two recurrences) | 7.7×10⁻⁴⁶ | 1.4×10⁻² | passes |
| e^{−21g} (three recurrences) | 2.1×10⁻⁶⁸ | 4×10⁻²⁵ | fails by 10¹⁶ |

A formation vertex built from at most two joint seven-channel recurrences fills the cap before any fitted mode enters the horizon. With a single recurrence it fills within ~10⁻²⁰ s, so σ_A = 1 exactly and Σ₀ coincides with the first labelable conserved charge. A vertex suppressed by three or more recurrences fails the abundance.

## 7. Formation isometry and a finite-register check of the ledger

**The map.** Formation mirrors the O.13 release isometry. Let P_∅ project onto unlabelled conserved charge for which the plasma supplies ρ_b/ε, and let W^form_α write the label, the cap, the initial count N_A = 0 and the plasma debit, with (W^form_α)†W^form_β = δ_αβ P_∅. Then:

- V^form|ψ⟩ = (I − P_∅)|ψ⟩|0⟩_M + (1/3) Σ_α |α⟩_M W^form_α P_∅|ψ⟩;
- (V^form)†V^form = I, by the same identity used in O.13.

**Single carrier (Part 1 of `ledger_model_check.py`).** On the physical subspace (L,c,r) ∈ {(none,0,0), (fine,1,0), (coarse,0,1)}, the formation map, the release map, and a hypothetical label-stripping map are each isometries to 3×10⁻¹⁶. Isometry therefore cannot be what forbids stripping; that work falls to the ledger rule.

**Reachability (Part 2).** The model has three carriers: two conserved charges and one neutral pair. A breadth-first search covers every sequence of formation, release, mixing, merging, heating and cooling, starting from the state just after formation:

| Operation set | Reachable states | Unlabelled charge reachable | Neutral pair ever allocated | Allocation-raising steps |
|---|---|---|---|---|
| Written operations, heating allowed | 96 | no | no | 0 |
| Plus a strip map, heating allowed | 288 | yes | no | 12 |
| Plus a strip map, cold only | 56 | yes | no | 0 |

**Reading.** With the written operations, n_∅ = 0 is absorbing at every temperature. A single strip map is enough to bring back re-formation once a hot plasma supplies the debit. In a cold environment the energy gate still blocks it, which is the second lock on released gas in galaxies.

## 8. The tied abundance against BAO, CMB and supernovae

This test fixes Ω_c/Ω_b in the frozen-η release model and refits. The likelihood is the bundle's (DESI DR2 BAO, compressed Planck priors, DES-SN5YR or Pantheon+ with the low-redshift offset). Tying the ratio leaves two free parameters, ω_b and σ_M. ΛCDM on the same likelihood has three. Scripts: `test_tied_abundance.py` and `lcdm_reference.py` in "Dark energy prediction tests".

| Data | ΛCDM (3 free) | Tied 5.321 (2 free) | Tied 5.333 (2 free) | Ratio free (3 free) |
|---|---|---|---|---|
| BAO + CMB | 14.92 | 13.37 | 12.88 | 12.40 |
| + DES-SN5YR, offset | 1641.80 | 1640.54 | 1640.00 | 1639.42 |
| + Pantheon+, offset | 1401.42 | 1400.96 | 1400.37 | 1399.64 |

**Constraint on the ratio.** The BAO + CMB profile gives Ω_c/Ω_b = 5.362 ± 0.041 inside the release model. The formation value 5.333 sits 0.70σ low, and the bare 1/ε = 5.321 sits 0.99σ low. For comparison, ΛCDM's best ratio on the same data is 5.297.

**Reading.** With one fewer free parameter than ΛCDM, the tied model fits better on every data combination: by Δχ² = 2.0 on BAO + CMB, 1.8 with DES, and 1.05 with Pantheon+.

**Full-likelihood follow-up** ("Full Planck tied abundance"). With Planck 2018 high-ℓ TT, TE and EE in place of the compressed priors, and the lensing deficit of the released share included (A_L,eff = 0.979), the tied model gives 2226.90 against ΛCDM's 2226.77 on Planck + DESI + DES. That is a match with one fewer parameter, not a better fit. The compressed advantage is the background part; the lensing deficit costs the same amount against PR3 plik.

**Caveats.**
- The compressed priors carry no lensing information. The full-likelihood follow-up supersedes the Δχ² values above.
- The release scale σ_M is fitted, as in the earlier dark-energy note.
- The 0.24% cap-mass shift was derived after the Planck value was known. Its sign and size follow from helium binding and were not adjusted.

## Formation theorem (manuscript wording)

> **Formation theorem.** Let n_∅ be the density of conserved baryonic charge carried without a source label. The formation map copies the Lagrangian identity of that charge into the capacity ledger, assigns the cap M_A/ε with M_A evaluated on Σ₀, starts the source count at N_A = 0, and draws the energy ρ_b/ε from the thermal plasma. Thermal pairs carry no net conserved charge and source nothing. After formation, n_∅ = 0. The local label operations preserve, release or merge labels; carrier loss moves a carrier to the coarse label of its retained carrier; descendants inherit their parent's label; and net baryon number is conserved below the sphaleron freeze-out temperature. Hence n_∅ remains zero, formation has no support after Σ₀ at any later temperature, and the committed stock decreases only through the one-signed marked drain.

## What remains open

1. **The formation vertex.** It must exist, act only on unlabelled conserved charge, and carry a per-tick weight above e^{−16.1g}, meaning no more than two joint recurrences. Whether quark-level charge is labelable decides whether Σ₀ sits at sphaleron freeze-out or at the QCD crossover.
2. **The explicit ledger rule for carrier loss** (fine label to coarse label, coarse cap equal to retained R). This is drafted in `formation_insert.tex`.
3. **The thermodynamic status of committed entropy.** The manuscript does not fix its record scale or sign. No result here depends on it after the second pass, but any Landauer-type claim does.
4. **The condensate realization of H.7**, including exact number U(1) apart from the drain. The Noether identification inherits its conditional status.

## Files

| File | Contents |
|---|---|
| `formation_check.py`, `formation_check_output.txt` | Substrate scale, condensate T_c, first-pass second-law table (withdrawn), epochs and debits, pair persistence, cap mass |
| `stress_transfer_check.py`, `stress_transfer_output.txt` | Background integration through plasma-paid formation |
| `pricing_and_vertex_check.py`, `pricing_and_vertex_output.txt` | Record-scale dependence of the withdrawn floor, renewal entropy export, vertex weight bound |
| `formation_insert.tex` | Insertion-ready Appendix O.15 with the formation isometry, status-table row, a §20 sentence on the tied fit, and a P.8 item (compiles) |
| `ledger_model_check.py`, `ledger_model_output.txt` | Isometry checks and reachability enumeration for the label ledger |
| `../Dark energy prediction tests/test_tied_abundance.py`, `tied_*.jsonl`, `lcdm_reference.py`, `lcdm_reference.jsonl` | Tied-abundance fits and the ΛCDM reference |
