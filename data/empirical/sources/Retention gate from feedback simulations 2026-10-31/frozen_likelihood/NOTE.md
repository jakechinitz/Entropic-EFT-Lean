# Frozen-history likelihood (2026-10-31)

The release history is fixed with no fitted parameter:
- pre-reionization gate: the Renaissance occupation, as a mixture of sharp mass gates (`make_frozen.py`);
- the six measured kernels (the default uses their mean history);
- post-reionization gate: 30 km/s.

z_re is the midpoint of the CAMB reionization history implied by the fitted tau (`q.get_zre()`). Histories at z_re = 7.0, 7.33, 7.66, 8.0, 8.4 and 8.8 are interpolated linearly.

Free parameters: omega_b, ln As, n_s, tau, plus the calibration where it is free. That is four cosmological parameters, against six for LCDM.

Harness: `harness_frozen_tie.py`, the one-harness likelihood of `/home/claude/cos/harness.py` (model GEO, linear-depletion background with its own lensing). The data are Planck plik-lite with 2 low-ell TT bins, the tau prior 0.0506 +- 0.0086, DESI DR2 and DES-Dovekie.

| Configuration | LCDM | Frozen release | Delta chi2 | z_re | tau | I_rel | H0 |
|---|---|---|---|---|---|---|---|
| Dovekie, mnu = 0.06, nonlinear, calibration free | 2239.031 | 2240.100 | +1.07 | 8.12 | 0.0587 | 92.0 | 68.42 |
| Low-z offset, mnu = 0, nonlinear, calibration fixed | 2226.767 | 2226.483 | -0.28 | 7.89 | 0.0565 | 93.7 | 68.89 |

Robustness (first configuration):

| Variant | chi2 | Notes |
|---|---|---|
| Kernel v14 R/4 | 2240.16 | |
| Kernel v12 R/4 | 2240.32 | |
| Post-reionization gate 35 km/s | 2240.19 | Coarse histories with a fine-grid offset correction; z_re clipped at 7.66 |
| Post-reionization gate 25 km/s | 2241.66 | z_re 8.94, tau 0.067 |
| z_re held at 7.66, not tied to tau | 2259.18 (+20.2) | The alternative configuration gives 2230.74 (+4.0) |

**Reading.** With z_re tied to tau, the frozen history fits as well as LCDM with two fewer parameters (Delta AIC -2.9 and -4.3).

The tie is physical, since tau measures z_re. It carries the fit. The data select I_rel near 92, and the tau-z_re link reaches that value at the LCDM best-fit tau.

**Prediction.** tau and Omega_Lambda are correlated. Earlier reionization means less release.

**a0.** a0 = eps c H0 gives 1.249e-10 from the first fit and 1.258e-10 from the second. The astrophysical chain alone gives (1.27 +- 0.04)e-10.
