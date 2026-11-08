# Dwarfs at the level of LCDM: support rule plus release gate (2026-10-28, evening)

## Files

| File | Contents |
|---|---|
| `score_runs.py`, `score_runs_output.txt` | Relaxed class from the contact-dynamics harness |
| `gate.py` | Release-gate crossing for each dwarf's main progenitor |
| `score_gate.py`, `score_gate_output.txt` | Combined rule |
| `runs/*_reg.json` | `dsph_W.py` runs for the 11 self-dominated dwarfs |

The runs use the settings of the 2026-10-26 classical rerun: paper register 0.9 V_f^2, supernova coupling 0.1, z_start = 6. Each run takes LVDB stellar mass and radius, the abundance-matched M200 and t_trunc = tau_90. The harness reproduces the earlier Draco run exactly (rho150 0.583, offset +0.16).

## Steps

1. **Relaxed class from the theory's own contact dynamics, in place of law + 0.08 dex.**
   - chi^2 30.7, essentially unchanged from 31.0.
   - Eridanus II and Canes Venatici I and II still relax fully, so the work register does not prevent it.
2. **Combined rule.**
   - The rule: a dwarf's stock relaxes only if
     - its own field dominates (the support rule), and
     - its main progenitor crossed the release gate of Section 20: V_vir >= 17 km/s before z_re = 7.66, or >= 30 km/s after.
   - Otherwise the stock keeps its committed, CDM-like allocation.
   - Gate crossing uses the Fakhouri et al. 2010 mean accretion history from the abundance-matched M200.

| Gate before z_re | Rule | LCDM + heating | Plain CDM |
|---|---|---|---|
| 17 km/s (reference gate) | **21.7** | 24.0 | 30.0 |
| 14 km/s (measured-kernel gate) | 25.4 | 24.0 | 30.0 |

chi^2 is over 22 dwarfs.

## Classification

| Class | Dwarfs |
|---|---|
| Sub-gate, self-dominated (retained) | Eridanus II, Canes Venatici II |
| Retained when M200 is 0.1 dex lower | Canes Venatici I (adds Canes Venatici I) |
| Gate-crossing, self-dominated (relaxed) | Tucana, Cetus, Leo I, Leo II, Fornax, Sculptor, Andromeda VI, Andromeda II |

- The classification of Eridanus II and Canes Venatici II holds for halo masses shifted by ±0.2 dex.
- The eight classical GravSphere dwarfs all crossed the gate, so their rho150 result (chi^2 10.4) is unchanged.

## Status

The gate condition adds no parameter. The 17 km/s gate and the z_re = 7.66 epoch are the cosmology sector's reference values.

It does choose one branch of a fork the paper leaves open. Section 20 says the low-mass behaviour "depends on whether the source remains in the saturated source-associated phase or exits it through the collective carrier-loss channel". Appendix O.3 is titled "Source-associated capacity after carrier loss". The dwarf data select:
- **Saturated, committed phase:** halos that never crossed the gate. Their stock is CDM-like.
- **Response stock:** halos that crossed it. Their stock relaxes where the carrier has support.

The paragraph in Section 20 that assigns sub-gate allocations to the response law would change accordingly.

## Remaining misses

- **Hercules:** every model misses it; it is tidally disrupting.
- **Canes Venatici I:** relaxed, pull +2.0. It sits 0.02 dex in V_vir above the gate.
