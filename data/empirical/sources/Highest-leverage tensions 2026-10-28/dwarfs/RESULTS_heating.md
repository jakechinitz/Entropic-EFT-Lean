# Satellite support rule vs LCDM + supernova heating on the classical dSphs (2026-10-28)

Script: `heat.py`; output: `heat_output.txt`.

The standard LCDM account of dSph central densities is dark-matter heating by supernova-driven gas outflows. It
is implemented here with coreNFW (Read et al. 2016) at its published calibration: kappa = 0.04, eta = 1.75, and
t_SF = 13.8 Gyr minus the truncation time. Both models use the same halos as the 2026-10-26 rerun, and both are
scored on the GravSphere rho(150 pc) with the same error model. Nothing is fitted.

## Results

| Model | chi^2 (8 dSphs) |
|---|---|
| Plain NFW | 16.4 |
| LCDM + heating | 11.9 |
| Support rule | 10.5 |

The two explanations differ where field dominance and star-formation duration disagree:

| Dwarf | Configuration | Rule predicts | Heating predicts | Observed | Favours |
|---|---|---|---|---|---|
| Carina | host-dominated, star formation until 2.8 Gyr ago | dense, 1.24 | cored, 0.73 | 1.16 | rule (chi^2 0.05 vs 2.51) |
| Leo II | self-dominated, star formation ended 6.3 Gyr ago | relaxed, 0.95 | 1.20 | 1.84 | heating (3.0 vs 5.1) |
| Fornax | self-dominated, star formation until recently | relaxed, 1.50 (runs) | 0.93 | 0.79 | heating (0.19 vs 1.92) |
| Draco | host-dominated, old | dense, 1.54 | 1.40 | 2.36 | rule (2.65 vs 4.00) |
| Sculptor | boundary, old | relaxed, 1.30 | 1.80 | 1.49 | rule (0.15 vs 0.44) |

## Verdict

A tie: Delta chi^2 = 1.4 in favour of the rule over 8 dwarfs, with no free parameters in either model. The
classical sample cannot separate the two accounts.

## What would

The two accounts give opposite predictions in two classes:

1. **Host-dominated dwarfs with extended star formation.**
   - The rule predicts dense, cuspy centres.
   - Heating predicts cores.
   - Carina is the only classical example.
2. **Self-dominated (isolated or distant) dwarfs with short, old star formation.**
   - The rule predicts relaxed, cored centres.
   - Heating predicts cusps.
   - Leo II currently counts against the rule.
   - Eridanus II's central star cluster has been used to argue for a core.
   - Tucana's central density is disputed between spectroscopic samples.

A registered list of central-density predictions for the second class is the decisive test. Candidates are
Eridanus II, Tucana, Cetus and the distant M31 satellites. Registration requires verified structural and
star-formation inputs for each target.
