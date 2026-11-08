# Preregistration: retained stock vs ΛCDM (NFW) for Crater II and Antlia 2

Written 2026-09-27, before any ΛCDM run or any Antlia 2 tidal run. Frozen once hashed.

## Question
How much does each model pay, in marginal likelihood, to reproduce the present-day dispersion, size, stellar mass (and, for Crater II, tail fraction) of Crater II and Antlia 2 on their measured orbits?

## Models
**Stock theory.** Milky Way = baryons (Hernquist bulge 1e10, a = 0.6 kpc; exponential disk 5e10, h = 2.6 kpc; spherical) plus retained RAR stock capped at C_R = 14 (module mw.py). Satellite = Plummer stars plus the retained isolated-RAR stock of the progenitor's stars, a0 = 1.231e-10 m s^-2, C_R = 3000, Gaussian taper at 12 kpc (Crater II) or 20 kpc (Antlia 2). No relaxation of the stock. No halo parameters.

**ΛCDM.** Milky Way = the same baryons plus NFW halo M200 = 1.2e12, c = 10 (mw_lcdm.py). Satellite = Plummer stars plus NFW subhalo, Gaussian taper at r200. Halo mass prior: lognormal around the Moster et al. (2013) stellar-to-halo relation evaluated at the progenitor stellar mass, 0.3 dex scatter, sampled at -0.3, 0, +0.3 dex. Concentration: Dutton & Macciò (2014) z = 0 median, log10 c = 0.905 - 0.101 log10(M200 / 1e12 h^-1), h = 0.7.

## Shared machinery
Same N-body code for both models: collisionless particles, monopole self-gravity about the density centre, full Milky Way field, leapfrog dt = 1 Myr, softening 0.03 kpc, 40k dark/stock particles and 10k star tracers. Static Milky Way, no LMC, no dynamical friction. Orbits from present phase space integrated in each model's own Milky Way. Each run starts at an apocentre three pericentres before the present and records the present-phase state after 1, 2 and 3 pericentres.

Inputs. Crater II: RA 177.310, Dec -18.413, D 117.5 kpc, v_los 87.5 km/s, PM (-0.07, -0.11) mas/yr. Antlia 2: RA 143.8868, Dec -36.7673, D 132 kpc, v_los 290.7 km/s, PM (-0.095, 0.059) mas/yr (Torrealba et al. 2019). Nominal orbits only.

## Shared priors on the progenitor
Stellar mass: 1, 2 or 4 times the present value, equal weight.
Stellar size: grid 0.7, 1.0, 1.5 times the present R_h, weighted by a size–mass prior log10 R_h[kpc] = log10(0.30) + 0.25 log10(M*/1e6), scatter 0.25 dex.
Number of pericentres since infall: 1, 2 or 3, equal weight.

## Data and likelihood
Crater II: sigma_los = 2.7 ± 0.3 km/s; R_h = 1.066 ± 0.084 kpc; M* = 3.2e5 ± 1.0e5; tail fraction (stars beyond 3 R_h within 14.4 kpc, 3D) = 0.23 ± 0.08.
Antlia 2: sigma_los = 6.0 ± 0.4 km/s (Ji et al. 2021, as quoted; sensitivity case 5.71 ± 1.08, Torrealba et al. 2019); R_h = 2.92 ± 0.31 kpc; M* = 8.8e5 ± 2.6e5.
Model sigma_los from bound stars within 1.5 R_h (projected, line of sight from the Sun). A 10% modelling error is added in quadrature to sigma and R_h. Gaussian likelihood; a system with bound star fraction below 1% has L = 0.
Marginal likelihood Z = prior-weighted sum over the grid. Report Z for each model and dwarf, the Bayes factor stock/ΛCDM, and the best-fitting grid point for each.

## Checks
Isolated NFW satellite must hold sigma and R_h within 5% over 3 Gyr. Report whatever the comparison gives.
