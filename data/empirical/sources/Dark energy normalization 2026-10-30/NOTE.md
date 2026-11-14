# Dark-energy normalization from first principles: a first attempt (2026-10-30)

**Question.** Can I_rel, and with it Ω_Λ and H0, be predicted without fitting? With the abundance tied, ω_Λ = η* ω_c I_rel. Flatness then gives h from I_rel alone. The CMB, BAO and SN data need I_rel ≈ 94–96 (h ≈ 0.69). The open input is the retention gate: which halos hold gas that carries records. I tried to fix it from the theory instead of choosing it.

## 1. The gate from the carrier criterion (`cooling_gate.py`)

**Criterion.** Section 18 says gas holds records only if it can cool: t_cool < t_dyn. I applied this to primordial gas at the mean virial density:
- collisional-ionization equilibrium;
- atomic H/He cooling (Katz, Weinberg & Hernquist 1996 rates) plus Compton cooling on the CMB;
- no H2 and no UV background.

**Result.**
- T_gate = 0.99–1.07×10⁴ K for z = 30–8. This is robust, set by the steep rise of H line cooling.
- With the gas's own CIE ionization state (μ = 1.22), V_gate = 11.6–12.0 km/s.
- The paper's reference 17 km/s is the same temperature with the ionized convention, μ = 0.59. The convention alone moves the gate by a factor 1.44 in velocity.

## 2. The gate measured in the hydro run (`gate_from_run.py`)

**Method.** I used the FOF catalogues of the 2026-10-04 Gadget-4 run (Release zoom/run, 48 snapshots, z = 15–6, atomic cooling and Springel–Hernquist star formation). For each group I asked whether it holds condensed baryons: star-forming gas or stars.

**Result.** The fraction with condensed baryons reaches one half at:

| z | V50 (km/s) | Groups (with condensed baryons) |
|---|---|---|
| 11–15 | 8.6 | 1194 (66) |
| 9–11 | 8.9 | 2625 (126) |
| 7.5–9 | 9.3 | 5066 (190) |
| 6–7.5 | 10.2 | 11672 (300) |

The transition is sharp, with a logistic width of 0.03 dex. Central gas densities exceed the mean virial density, so gas condenses below the mean-density estimate. FOF masses slightly exceed virial masses, which makes these V50 values upper limits.

## 3. I_rel, Ω_Λ and h against the gate (`irel_gate.py`)

**Setup.** First-entry histories at each pre-reionization gate, with the 30 km/s post-reionization gate and z_re = 7.66. Convolved with the measured kernels (K0 = 0.53–0.70, f = 2.2–4.9). The kernel choice moves I_rel by only ±3%; the gate dominates.

| Pre-reionization gate | I_rel | Implied h | Implied Ω_Λ |
|---|---|---|---|
| 9 km/s (run, condensation) | 129–136 | 0.77–0.79 | 0.77 |
| 10 km/s (run, condensation) | 119–125 | 0.75–0.77 | 0.76 |
| 12 km/s (cooling criterion, μ = 1.22) | 104–110 | 0.71–0.73 | 0.73 |
| **14 km/s (required)** | **92–98** | **0.69–0.70** | **0.71** |
| 17 km/s (paper reference, μ = 0.59) | 81–85 | 0.65–0.67 | 0.68 |

The halo mass at 14 km/s is 6.6×10⁷ M☉ at z = 8, 4.9×10⁷ at z = 10 and 2.8×10⁷ at z = 15.

## Reading

1. **First-principles gates overshoot.** Both gates derived from the theory's carrier criterion without feedback, the cooling estimate (12 km/s) and the run's own condensation (9–10 km/s), give too much release: I_rel 15–40% above what the CMB requires. H0 would come out 72–79.
2. **The data need a 14 km/s gate.** That is T_vir ≈ 1.4×10⁴ K, or about 5×10⁷ M☉ at z ≈ 10. Halos below this must not hold mixed, record-carrying gas.
   - **Physics that could raise the gate:** supernova feedback, photoheating in ionized bubbles before the global z_re, and Lyman–Werner and X-ray backgrounds. All of these raise the effective gate in this direction.
   - **What the run lacks:** feedback, H2 and patchy reionization.
   - **Inferred limits:** observational minimum halo masses for star formation during reionization (faint-end UV luminosity functions) are 10⁸–10⁹ M☉. That is 16–35 km/s at z ≈ 8, which brackets the requirement from above.
3. **The normalization is not locked in.** The theory turns Ω_Λ into an astrophysical census: the (1+z)³-weighted fraction of baryons that entered retaining, mixing galaxies. Its value depends on early-galaxy feedback, which is uncertain at the ±30% level in I_rel.
4. **It does yield a consistency prediction.** Given the observed Ω_Λ and H0, the effective threshold for record-carrying gas retention at z ≈ 8–15 must be V ≈ 14 km/s (M ≈ 5×10⁷ M☉ at z = 10). That links dark energy to the faintest first galaxies. JWST faint-end luminosity functions, reionization histories and 21-cm data can test it.

## Limits

- **Resolution:** about 10³ gas particles per host, SPH, and no feedback or H2.
- **Cosmology:** the first-entry history uses a fixed reference cosmology.
- **Post-reionization gate:** 30 km/s and z_re are taken from the literature, not derived.
- **Labels:** the label definition was not revisited here. The 2026-10-04 note shows labels move I_rel by about ±20%.

## Files

- `cooling_gate.py`, `cooling_gate.json`
- `gate_from_run.py`, `gate_from_run.json`
- `irel_gate.py`, `irel_gate.json`
- `sigmaM.py` (an Eisenstein–Hu σ(M) substitute; it reproduces FZ_ref to Monte Carlo noise and I_rel to 0.3)
- `o12_release.py` (the Release zoom copy, with its path made local)
