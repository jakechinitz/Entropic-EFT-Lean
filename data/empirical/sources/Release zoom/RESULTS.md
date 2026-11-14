# Fixing the release scale: the O.12 kernel against the full likelihood, and a first self-gravitating zoom

Date: 2026-10-04. This folder replaces the fitted release scale σ_M with the physical O.12 release history and measures the mixing kernel in a cosmological hydrodynamic run.

## 1. The O.12 release history, reimplemented (`o12_release.py`)

The release history has three ingredients:
- an absorbing first-entry excursion set, with retained-well gates of 17 km/s before z_re = 7.66 and 30 km/s after;
- an Eisenstein–Hu σ(M) normalized to σ₈ = 0.810;
- the kernel K_mix = 1 − exp(−τ/f t_dyn).

The reimplementation is checked against the manuscript's tables, with 3×10⁵ trajectories and Brownian-bridge maxima:

| z | 10 | 8 | 7 | 6 | 5 | 3 | 1 | 0 |
|---|---|---|---|---|---|---|---|---|
| F_Z (this code) | 0.0137 | 0.0389 | 0.0517 | 0.0694 | 0.1032 | 0.2411 | 0.5063 | 0.6700 |
| F_Z (manuscript) | 0.0138 | 0.0388 | 0.0522 | 0.0704 | 0.104 | 0.243 | 0.509 | 0.671 |

| f | 0 | 0.25 | 0.5 | 0.75 | 1 | 2 |
|---|---|---|---|---|---|---|
| I_rel (this code) | 102.4 | 94.9 | 88.8 | 83.8 | 79.4 | 66.3 |
| I_rel (manuscript) | 103.7 | 96.3 | 90.2 | 85.0 | 80.6 | 67.3 |

The code reproduces the manuscript to 1–1.5%. The residual comes from the coarser redshift grid (0.01 here against 0.0025).

## 2. What the full likelihood requires of the kernel (`zoom_fit.py`)

The setup is the "Full Planck tied abundance" pipeline: Planck 2018 high-ℓ TT,TE,EE, DESI DR2 BAO, DES-SN5YR and A_L = 0.979. The ratio is tied at Ω_c/Ω_b = 5.333, and f replaces σ_M as the single release parameter.

| Model | Free | χ² (P+DESI+DES) | f | h | Ω_Λ | I_rel |
|---|---|---|---|---|---|---|
| ΛCDM | 6 | 2226.77 | – | 0.677 | – | – |
| Tied, bundle release (σ_M fitted) | 5 | 2226.90 | – | 0.692 | – | – |
| Tied, O.12 release (f fitted) | 5 | **2227.33** | **0.283** | 0.689 | 0.707 | 94.2 |
| Tied, O.12 release, f = 0.5 | 4 | 2272.64 | 0.5 fixed | 0.683 | | |
| Tied, O.12 release, f = 0.75 | 4 | 2416.39 | 0.75 fixed | 0.676 | | |

**Reading.**
- **The O.12 shape fits.** It matches ΛCDM to Δχ² = +0.6 with one fewer parameter.
- **The data fix the kernel sharply.** With the abundance tied, h follows from ω_b and the release integral. The CMB acoustic scale then pins I_rel, and the curvature of the profile gives f = 0.28 ± 0.03 at the reference gates.
- **Correction to O.12.** The manuscript places the Planck Ω_Λ = 0.685 at f = 0.75, but that value comes from a ΛCDM fit. Inside the release model, the full likelihood requires Ω_Λ = 0.707 and I_rel = 94.2, which is f = 0.28 at the reference gates. Mixing must complete in about a quarter of a dynamical time after first entry, or the gates must differ.
- **Gate degeneracy.** The gates move I_rel by several percent, as large as the f effect (O.12 lists the shifts). The data constrain the combination, I_rel ≈ 94, not f alone.

## 3. The cosmological run

Code: Gadget-4 (Springel et al. 2021), compiled with:
- PERIODIC, TreePM, SPH;
- primordial H/He cooling (Katz, Weinberg & Hernquist 1996), with the UV background off above z = 6;
- Springel & Hernquist (2003) star formation;
- on-the-fly FOF;
- N-GenIC 2LPT initial conditions at z = 63.

| Setting | Value |
|---|---|
| Box | 0.75 h⁻¹ comoving Mpc |
| Particles | 2×96³ |
| m_DM | 3.5×10⁴ h⁻¹ M☉ |
| m_gas | 6.5×10³ h⁻¹ M☉ |
| Snapshots | 48, every 15 Myr from z = 15 to z = 6 |
| Hardware | two cores |

Analysis (`kmix.py`):
- **Hosts.** Main progenitors first crossing V_c = 17 km/s.
- **Cohort.** The baryonic particles of each host at first entry.
- **Labels A.** FOF membership one dynamical time earlier. Ungrouped gas is labelled by its octant about the progenitor centre.
- **Partitions Y_t.** Shells × octants, or cubes of R_vir/2 or R_vir/4, all relative to the host centre and scaled to R_vir(t).
- **Mixing measure.** K_mix(τ) = 1 − [I(A;Y_t) − I_shuffled]/H(A), fitted to 1 − (1 − K₀)e^{−τ/τ_mix}, giving f = τ_mix/t_dyn(z_f).

Run log: started 15:19 UTC and reached z = 6 at 19:59 UTC. Star formation began near z ≈ 11. Configuration and FOF catalogs are in `run/`.

## 4. Measured kernels (`kmix_v17/v14/v12.json`, `kmix_summary.txt`)

Every host shows the same pattern. At entry, about half of the progenitor information on the coarse partitions is already gone (K₀ ≈ 0.5). The rest is lost on a timescale of 2–6 halo dynamical times.

| Gate | Hosts | Partition | K₀ | f (16–84%) | I_rel from this kernel | Required by the data |
|---|---|---|---|---|---|---|
| 17 km/s (reference) | 3 | shells × octants | 0.55 | 5.8 (3.9–5.8) | 75.4 | 94.2 |
| | | cubes R/2 | 0.49 | 4.2 (2.8–4.4) | 75.6 | |
| | | cubes R/4 | 0.56 | 6.0 (4.2–6.4) | 75.9 | |
| 14 km/s | 10 | shells × octants | 0.56 | 2.5 (1.8–3.9) | 96.7 | 94.2 |
| | | cubes R/2 | 0.53 | 2.2 (1.5–3.3) | 96.7 | |
| | | cubes R/4 | 0.58 | 3.9 (2.7–5.5) | 93.1 | |
| 12 km/s | 16 | shells × octants | 0.58 | 2.9 (1.9–3.6) | 108.0 | 94.2 |
| | | cubes R/2 | 0.56 | 2.5 (1.9–3.3) | 108.9 | |
| | | cubes R/4 | 0.70 | 4.9 (3.9–12) | 109.9 | |

Each I_rel uses the first-entry history at the same gate as the host selection (`effective_f.py`).

**Label sensitivity at 17 km/s:**
- Labelling two dynamical times before entry gives I_rel = 82–83.
- Dropping smooth-accretion labels (grouped gas only) gives K₀ ≈ 0.2–0.3 and I_rel = 57–65.

**Baseline sensitivity.** At the 12 km/s gate, hosts followed for at least three dynamical times give a median f of 3.1 on R/2 cubes, against 2.5 for all hosts.

## 5. Reading

1. **The O.12 kernel form survives contact with a self-gravitating run.** Release is cumulative and monotone after first entry. It includes an immediate share at entry and an exponential tail of a few dynamical times.
2. **At the manuscript's reference gate (17 km/s), the measured kernel is too slow.** It gives I_rel ≈ 76 against the required 94.2, about 20% short. As a pure exponential, the measured kernel is equivalent to f_eff = 1.2, against the f = 0.28 the data require.
3. **At a 14 km/s gate, the measured kernel reproduces the required integral (93–97).** That gate corresponds to a virial temperature of 1.4×10⁴ K, inside the usual range for atomic-cooling haloes.
4. **The zoom does not fix σ_M on its own.** It turns σ_M into two physical quantities the theory must specify: the effective retention gate and the definition of progenitor labels. The label choice alone moves I_rel by about ±20 at the reference gate. This counts as progress, since both are now physical and measurable, but it is not yet a zero-parameter prediction.
5. **What would settle it.** A resolved zoom (≥10⁴ gas particles per host) with molecular cooling, feedback, subgrid turbulent mixing and a UV background is needed. The gate should be read off gas retention, not imposed, and the progenitor labels fixed by the theory before the run.

## Limits

- **Resolution.** About 500–2,400 gas particles per host, and only 3 hosts at the reference gate.
- **SPH.** No subgrid diffusion. Coarse-partition interpenetration is captured, but kernel-scale mixing is not.
- **Missing physics.** No H₂ cooling, no feedback, and no UV background before z = 6. The gate is imposed in the host selection.
- **Background.** The excursion-set background uses the reference cosmology. The first-entry history is reimplemented, not the original code, and agrees with it to 1–1.5%.

