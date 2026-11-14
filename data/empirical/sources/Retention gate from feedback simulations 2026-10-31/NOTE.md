# Retention gate from feedback-resolved simulations (2026-10-31)

**Question.** Can the dark-energy normalization be tested with a retention gate taken from simulations that include feedback, so that no gate is chosen to match the target?

The O.12 chain is reused unchanged:
- first-entry excursion-set assembly;
- the six mixing kernels measured on the 12 and 14 km/s hosts of the Gadget-4 run;
- ω_Λ = η* ω_c I_rel;
- flatness.

Only the pre-reionization gate changes. It is now a halo **mass** taken from the literature, not a velocity derived or selected here.

## 1. Inputs

**Renaissance simulations** (Xu et al. 2016, ApJ 833, 84; arXiv:1604.07842).
- Physics: Enzo with radiative transfer (Moray), Pop III and metal-enriched star formation, radiative and supernova feedback, metal cooling, and Lyman–Werner backgrounds.
- Coverage: rare-peak, normal and void regions, run to z = 15, 12.5 and 8.
- Occupation result, in the authors' words: about 10% of halos of M_vir ~ 1e7 M☉ host recent (<20 Myr) star formation, about 50% by 1e8, and unity above 10^8.5. The fraction falls to zero near 7e6 M☉ (O'Shea et al. 2015). They describe it as "quite independent of redshift and region".

**Milky Way satellite census.**
- Nadler et al. 2020: M50 = 10^7.51 in peak mass, below 8.5e7 at 95%.
- Manwadkar & Kravtsov 2022 (GRUMPY): M50 = 3.6e7.
- Ultra-faint dwarfs form in halos as small as ~1e7 M☉.
- These numbers are peak masses. The mass when the stars formed is smaller, so as a high-redshift gate they are upper limits.

**Post-reionization gate and z_re.** 30 km/s (Okamoto et al. 2008) and z_re = 7.66 (Planck), as in O.12.

## 2. Method

- `gate_mass.py` replaces the pre-reionization velocity gate by a mass gate. It reproduces the archived 14 km/s values exactly.
- `grid_mass.py` computes I_rel for constant-mass gates from 10^6.5 to 10^9.0.
- A soft occupation curve f(M) is treated as a mixture of sharp gates, each trajectory drawing its own threshold. Since I_rel is linear in F_Z, this gives I_soft = ∫ df(M_g) I(M_g).
- The Renaissance curve is piecewise linear in log M through the published anchors: (10^6.85, 0), (1e7, 0.1), (1e8, 0.5), (10^8.5, 1).

## 3. Results (reference z_re = 7.66, post gate 30 km/s; I_rel range over the six kernels)

| Gate | I_rel | h | Ω_Λ |
|---|---|---|---|
| Sharp 1e7 | 142 (137–145) | 0.81 | 0.78 |
| Sharp 10^7.51 (satellite M50) | 107 (104–109) | 0.72 | 0.73 |
| Sharp 10^7.75 (the value that gives the target) | 94.2 | 0.690 | 0.706 |
| Sharp 1e8 (Renaissance 50% point alone) | 83 (80–84) | 0.66 | 0.68 |
| **Renaissance occupation curve** | **95.5 (92.3–97.4)** | **0.693** | **0.709** |
| Required by the likelihood | 94.2 ± 0.8 | 0.689 | 0.707 |

## 4. Uncertainty for the Renaissance-curve result (68%)

| Source | ΔI_rel |
|---|---|
| Measured kernels (six) | ±2.5 |
| Anchors of the occupation curve (81 variants: zero point, 10% level, 50% point and saturation mass) | +4 / −2.4 (16–84%) |
| z_re = 6.94–8.40 (Planck ±1σ): 100.8 / 89.8 | ±5.5 |
| Post-reionization gate 25–35 km/s: 100.4 / 91.8 | ±4.3 |
| **Total in quadrature** | **±8** |

**Result:** I_rel = 95.5 ± 8, Ω_Λ = 0.709 (+0.017/−0.019) and h = 0.693 ± 0.021, against the required 94.2, 0.707 and 0.689.

- The new gate is not the dominant error. The reionization redshift and the post-reionization gate dominate, and both are inputs O.12 already had.
- No input was adjusted to Λ. Renaissance (2016), the Planck z_re and Okamoto's gate all predate this calculation.

## 5. The identification question (the main caveat)

The result depends on what counts as a *retained well*.

**Reading A, sustained retention (used above).** A halo enters the release history when it holds condensed, star-forming gas that can mix.
- Release in O.12 is continuous mixing of progenitor labels in retained gas.
- The fraction of halos holding star-forming gas at a given time is the time-averaged retention fraction, i.e. the duty cycle.
- Renaissance's recent-star-formation occupation measures exactly that.
- This reading gives **0.709 ± 0.02**.

**Reading B, any stars ever.** Ultra-faint dwarfs form a few thousand solar masses of stars in halos of ~1e7 and then lose their gas.
- If every halo that ever formed a star counts, the satellite census puts the gate at or below 10^7.5 at formation.
- That gives **Ω_Λ ≥ 0.73**: at least 3–4% high, and more once formation mass falls below peak mass (0.78 at 1e7).

Section 18 counts stars as records. O.12's release needs retained gas that mixes. The theory has to state which applies. Reading A follows the mixing-kernel physics, and Reading B follows the record definition alone.

**Other caveats.**
- The occupation curve was read from the text, not digitized from the figure. The variants above cover that.
- The mixture model gives each trajectory a fixed threshold. Drawing independently per halo per epoch would raise entry somewhat.
- The kernels come from a run without feedback.
- The target 94.2 comes from the approximate PPF pipeline with z_re fixed.

## 6. Reading

With a feedback-resolved occupation from an independent simulation suite, the release normalization predicts Ω_Λ = 0.709 ± 0.02, against the 0.707 the data require. This is the first test of the normalization in which no gate is chosen to fit. It passes at ~3% precision under the sustained-retention reading, and overshoots by ≥3% under the any-stars reading.

What would sharpen it:
1. Fix the identification in the theory.
2. Tighten z_re, from the CMB optical depth or 21-cm.
3. Measure the post-reionization retention gate in the same simulations.
4. Ideally, measure K_mix in a feedback-resolved zoom.

## Files

- Code: `gate_mass.py`, `grid_mass.py`, `mixtures.py`, `renvar.py`, `runb.sh`, plus `o12_release.py` and `sigmaM.py` copied from the 2026-10-30 folder.
- Outputs:
  - `grid_ref.json` (z_re 7.66, post gate 30, six kernels);
  - `grid_zre70.json`;
  - `grid_vp25_mean.json`, `grid_vp35_mean.json` and `grid_zre84_mean.json` (kernel-mean only);
  - logs.

Sources:
- Xu et al. 2016, arXiv:1604.07842
- O'Shea et al. 2015, arXiv:1503.01110
- Nadler et al. 2020, arXiv:1912.03303
- Manwadkar & Kravtsov 2022, arXiv:2112.04511
- Benítez-Llambay & Frenk 2020, arXiv:2004.06124
