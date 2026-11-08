# Highest-leverage tensions, 2026-10-28

This folder addresses three open tensions from `Verification 2026-10-27/06_known_issues.md` and the 2026-10-25/26 prediction tests. Each subfolder holds its code, raw outputs and a RESULTS file. None of this has been applied to the manuscript. The proposed text changes in each RESULTS file are for Jake to decide.

| Item | Outcome | File |
|---|---|---|
| Dwarfs (K03/K04) | Resolved by a proposed satellite activity rule (a premise decision). Eight GravSphere dSphs give χ² = 10.4, against 17.2 for plain CDM and 44 for all relaxed. RAR offsets follow the same ratio (Spearman 0.83). | `dwarfs/RESULTS_dwarfs.md` |
| Cosmology (K01) | Reconciled. Every ΛCDM χ² in the paper is reproduced in one harness. The −0.515 sign does not survive standard data settings (Δχ² ≈ +1.2 to +2.7). A statistical tie survives. Most of the penalty is DESI DR2 BAO under the tied abundance. | `cosmology/RESULTS_K01.md` |
| Isolated-lens budget edge | Not resolved. A population forward model with the splashback-mass budget and a shared environment term gives the capped theory Δχ² ≈ +30 against NFW and +105 against the uncapped law. The data want a budget 3 to 6 times larger. | `lensing/RESULTS_lensing.md` |

External data were downloaded from public sources and are not copied here: DES-SN5YR and Dovekie from GitHub des-science, planck-lite-py from GitHub heatherprince, and the Brouwer 2021 ESD tables from kids.strw.leidenuniv.nl. `harness.py` and `fwd.py` expect them under `ext/` next to the code.
