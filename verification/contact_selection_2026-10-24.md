# Contact selection: scope (2026-10-24)

The research note "Physical basis of the contact rule" in the device folder
`02 Research/Contact rule physical basis 2026-10-24` describes the physics. Lean
proves the identities only. Premises not formalized:
- the stock field in baryon units is the cell occupation (n = g_s/g_b);
- the cells are in equipartition with the excess field;
- orbit populations exchange with the cells, at a free rate;
- cells exist only on active carriers (the candidate cluster gate).

Numerical evidence (3-D central-impulse contacts, Bose functional, 12 Gyr):
- Milky Way model: 0.019-0.024 dex rms from the RAR;
- dwarf: 0.025-0.030 dex;
- light-halo massive spiral: 0.051 dex.
Contacts conserve momentum and angular momentum to roundoff, and energy closes to 1e-3 V_f^2.

## Section 3: cluster and galaxy-sector identities (added later on 2026-10-24)

Eight further statements support the "Clusters" editions of the full paper
and the empirical paper:
- `occupation_is_enclosed_ratio`: for spherical shells, g_s/g_b equals M_s(<r)/M_b(<r).
- `clip_optimal`, `clip_monotone`: clipping the cumulative target at the budget
  is the closest admissible profile pointwise and preserves monotonicity.
- `lensing_stock_bound`: a finite stock S times the baryons reaches the deep-law
  excess surface density only if S >= (pi/4) sqrt(a0/g) - 1.
- `field_response_misses_clusters`: numerical check that an always-on response
  added to cohort stock overshoots the X-COP R500 median by more than 40%, and
  that the response alone falls short by at least 29%.
- `cohort_between_xcop`: 1 + k_C lies between the X-COP medians 6.10 and 6.45.
- `no_cells_no_bias`: bookkeeping; with zero cell free energy the bias term vanishes.
  The premise that cluster stock has no active-carrier cells is not formalized.
- `redshift_ratio_precision`: a 3-sigma separation of H(2.3)/H0 = 3.4648 from 3
  needs fractional precision between 4.4% and 4.5%.
The numerical statements check arithmetic on quoted inputs; they do not
derive the X-COP medians or the cosmological background.

Observed-cluster runs (device folder `02 Research/Bose contact observed clusters
2026-10-24`, seven X-COP clusters, 40 runs) apply the contact rule without a
cluster gate. With the galaxy-scaled work allowance (0.45 V_f^2), the mass inside
R500 falls to 55-84% of the no-contact control; with a 15,000 (km/s)^2 reserve it
stays at 98-99%. No theorem here selects either allowance or proves the gate.
