# Real-cluster tests of the Bose contact rule

24 October 2026. Final completed run set. Claude source snapshot: `Contact rule physical basis 2026-10-24`, findings.tex saved at 14:30 local time.

**Direct answer:** the supplied new Bose archive contained five galaxy runs and no observed-cluster run. This project now adds tests on seven observed X-COP clusters. These are data-conditioned survival experiments, not cluster formation predictions or independent fits of their total masses.

**Main result:** applying the common work scaling implied by the galaxy runs, with no cluster gate, leaves 54.7–84.4% of the no-contact mass inside R500 after 8–10 Gyr. A much smaller fixed work reserve is a separate assumption and preserves more mass. The results do not establish automatic cluster protection by the galaxy prescription.

## What was tested

All seven X-COP targets with released stellar profiles: A85, A1795, A2029, A2142, A2319, A644 and ZW1215. Gas and stellar mass profiles are taken from the previously archived release; the previously documented approximate stellar deprojection is retained. The X-ray hydrostatic NFW reconstruction sets the initial total mass. A smooth positive stock profile is fitted to total minus baryonic mass, with maximum total-mass fitting errors of 0.3–2.1% across the adopted measured interval. Isotropic Eddington initial states reproduce the input density to better than 0.08%.

For every cluster: ten Gyr with contacts off, one attempt per orbit, and three attempts per orbit. The same initial particles, fixed baryons, local a0 = 1.2307e-10 m/s², and initial available work of 15,000 (km/s)² per unit stock mass are used. No dispersion cutoff is applied. This is the saved Milky Way work allowance, not a work capacity newly derived for clusters. Claude’s saved galaxy budgets are themselves different for different benchmark galaxies.

The ten Gyr is exposure to a fixed present-day model, not a reconstruction of the clusters’ past. Cosmological evolution of H(z), accretion, assembly, gas redistribution and recharge are not evolved. These survival tests constrain the candidate relaxation prescription; they do not exclude a cosmological completion with a different formation history.

The particles and impulses are three-dimensional; gravity is spherical. The Bose functional derivative, nearest-neighbour selection, orbit-average acceptance, central impulses and register debit use Claude’s archived functions. A conservative regularization of the gravity integration is required for a trustworthy energy account; see the numerical audit below. There is no added second halo force.

## Equilibrium alone does not fit the cluster data

If the stock fully reached the galaxy Bose/RAR equilibrium, the total mass at the observed R500 would be 25–46% below the X-ray reconstructed mass. The required removal of stock from that aperture is 31–52%. This statement uses the measured baryons and the response law, not a simulation.

| Cluster | Equilibrium total mass / X-ray mass | Equilibrium stock / required stock |
|---|---:|---:|
| A85 | 0.687 | 0.630 |
| A1795 | 0.685 | 0.631 |
| A2029 | 0.626 | 0.562 |
| A2142 | 0.662 | 0.596 |
| A2319 | 0.753 | 0.693 |
| A644 | 0.637 | 0.579 |
| ZW1215 | 0.540 | 0.484 |

Using a0(z) = a0(0) H(z)/H0 at these low redshifts changes the total-mass ratios by only about 0.008–0.013; it does not remove this mismatch. The sensitivity uses the data reduction’s flat Omega_m = 0.3 background and does not retune the simulations.

For the five overlapping MENeaCS lensing reconstructions the same equilibrium gives 0.475–0.801 of their central published NFW M500. These lensing estimates have substantial errors and modelling assumptions. This is a central-value comparison at each lensing aperture, not a joint likelihood or a claimed statistical exclusion. In particular the existing HSE/lensing disagreements in A1795 and A2029 have not been solved by this experiment.

## The scaling implied by the saved galaxy budgets

The Milky Way, dwarf and massive-spiral simulations use different dimensional work budgets, but they correspond respectively to 0.447, 0.452 and 0.450 times Vf². Thus applying the same dimensionless allowance means D = 0.45 sqrt(G M_b,total a0), rather than assigning every cluster the Milky Way’s fixed 15,000. This was identified during the audit and prompted an additional fourteen-run test on all seven clusters, at both rates. The coefficient is inferred from the simulation choices, not derived from the microscopic theory.

M_b,total is the asymptotic baryon mass of the explicit finite profile completion. It is an assumed exterior continuation. Even using only the measured baryons inside R500, the same allocation exceeds the mechanical cost of the full RAR endpoint in every cluster. Hence the small-budget obstruction cannot simply be imported from the galaxies under this scaling.

With this shared dimensionless allocation and no temperature gate, the late-time R500 mass is 54.7–84.4% of the no-contact control across the fourteen runs.

| Cluster | Shared work [(km/s)²] | R500/control, 1/orbit | R500/control, 3/orbit | 0.3 R500/control, 3/orbit |
|---|---:|---:|---:|---:|
| A85 | 767414 | 0.831 | 0.787 | 0.424 |
| A1795 | 663894 | 0.825 | 0.726 | 0.352 |
| A2029 | 955978 | 0.798 | 0.666 | 0.345 |
| A2142 | 1055236 | 0.823 | 0.774 | 0.440 |
| A2319 | 954420 | 0.844 | 0.746 | 0.319 |
| A644 | 706127 | 0.801 | 0.697 | 0.330 |
| ZW1215 | 719672 | 0.779 | 0.547 | 0.404 |

**Interpretation:** in this tested extrapolation, the ungated galaxy prescription does not preserve the observed cluster profiles. The two work allocations are different effective assumptions. The small-reserve results below cannot be used to claim that the galaxy-scaled prescription automatically protects clusters. A cluster-protection claim needs a physically selected capacity/recharge law or a kinetic suppression mechanism, together with a formation history, and must preserve the resolved radial profiles as well as the aperture mass.

## Restricted low-work evolution

With the small shared reserve, the late-time total mass at R500 is 97.9–99.1% of the matched no-contact control across all seven clusters and both nonzero rates. At 0.3 R500 the range is 91.7–104.6%. These are 8–10 Gyr averages, not error bars or ensemble probabilities. Consecutive saved times are correlated.

| Cluster | R500: 1 attempt/orbit / control | R500: 3 attempts/orbit / control | 0.3 R500: 3 attempts/orbit / control |
|---|---:|---:|---:|
| A85 | 0.989 | 0.979 | 0.917 |
| A1795 | 0.983 | 0.980 | 0.925 |
| A2029 | 0.989 | 0.986 | 0.938 |
| A2142 | 0.991 | 0.988 | 0.976 |
| A2319 | 0.989 | 0.985 | 0.928 |
| A644 | 0.991 | 0.990 | 0.984 |
| ZW1215 | 0.981 | 0.988 | 1.046 |

The reserve is rapidly exhausted, but contacts do not literally cease: cooling events can recharge it, and redistribution can continue with little net energy input. Thus the observed survival is not equivalent to proving every radial bin is fixed. The smallest-radius bins are especially sensitive to particle sampling.

### Larger-reserve and resolution checks

The following table compares the same three-attempt rule under the galaxy-scaled reserve and with twice as many particles, another seed, and a smaller numerical smoothing length. The more demanding shared-scaling case received the resolution checks after the common galaxy normalization was identified. These are sensitivity checks; no best-fitting reserve or rate is selected.

| Cluster | Check | R500 / matched control | 0.3 R500 / matched control |
|---|---|---:|---:|
| A1795 | 2,000 particles; small reserve | 0.980 | 0.925 |
| A1795 | 2,000 particles; galaxy-scaled reserve | 0.726 | 0.352 |
| A1795 | 4,000 particles; galaxy-scaled; seed 2; 2.5 kpc smoothing | 0.799 | 0.370 |
| ZW1215 | 2,000 particles; small reserve | 0.988 | 1.046 |
| ZW1215 | 2,000 particles; galaxy-scaled reserve | 0.547 | 0.404 |
| ZW1215 | 4,000 particles; galaxy-scaled; seed 2; 2.5 kpc smoothing | 0.507 | 0.356 |

The 0.05 Myr A1795 galaxy-scaled check gives R500/control = 0.747 and 0.3 R500/control = 0.379. It is compared with the 0.1 Myr no-contact control. Stochastic trajectories need not agree point by point. The higher-particle checks vary seed and smoothing together, so they test robustness rather than isolating a convergence order or measuring seed variance.

## Why a limited reserve can help

For a spherical isolated stationary stock with fixed baryons and zero boundary pressure, the scalar virial identity gives

\[2K=G\int\frac{M_s(r)+M_b(r)}r\,dM_s,\qquad E=K+W_s+W_b.\]

Apply this to the initial finite stock and to the monotone galaxy-response profile clipped at that same total stock mass. With the stated profile completions, reaching that full stationary endpoint requires 265,000–473,000 (km/s)² per unit stock mass: about 18–32 times the small reserve. Doubling the endpoint quadrature grid changes these values by less than one part per million.

This is a necessary energy requirement under the simulated register-only mechanical accounting, not a proof of equilibrium existence, a bound on every possible partial rearrangement, or a formation calculation. It assumes no independent cell/bath energy supply, escaping stock, changing baryons or replenishment. A cluster cannot pay that full cost from the chosen reserve; nevertheless it can rearrange its interior while keeping almost the same total energy.

**A fixed limited-work mechanism remains an alternative effective assumption.** A fixed specific reserve is much smaller relative to a cluster’s binding energy than to a galaxy’s. It is not the dimensionless work scaling implied by the saved galaxy runs. The test does not establish why a fixed reserve would be universal, how much collapse recharges it, or which parts of the stock can exchange it. Those questions determine whether this alternative could select cluster protection. A kinetic carrier gate remains a separate possible ingredient and has not been derived here.

## Numerical audit

There are 40 completed accepted runs: 21 low-work/control, fourteen galaxy-scaled work, four particle/seed/smoothing checks and one timestep check. The maximum mechanical energy-accounting error is 0.192% of the initial reserve. The largest single-contact-interval relative momentum and angular-momentum residuals are 3.54e-17 and 1.62e-17. The force agrees with a finite-difference derivative of its diagnosed energy to about 3e-7 in the validation state. The particle/seed checks concern the galaxy-scaled case; this is still a screening test with limited resolution checks, not a formal convergence or likelihood claim.

The original grid-force/exact-shell-energy pairing generated errors large enough to matter for a small reserve. An unsoftened conservative follow-up then exposed unresolved central passages. Those preliminary runs, an adapter coding failure, and interrupted checks are preserved and excluded from the final quantitative results. The final self-energy uses -G m² sum_i i/sqrt(r_i²+epsilon²), with its exact radial force. The baryon force is the derivative of the same interpolated potential used in the energy account. The orbit calculation uses the corresponding softened monopole. At the smallest compared data radius the regularization changes the continuum stock force by less than 0.4%.

This is a controlled numerical completion of the spherical model, not evidence for new short-distance physics. The tests do not establish full three-dimensional convergence of a contact operator: a nearest-neighbour macroparticle prescription still needs a physical continuum rate and interaction-range interpretation.

## What this establishes and what remains open

- The new Bose contact now has actual observed-cluster tests, using a shared rate and work allowance rather than individually tuned cluster gates.
- Limited available work can obstruct full galaxy-like relaxation of a cluster and can preserve much of its outer mass in these controlled runs. Internal profile changes and budget sensitivity must be retained in the assessment.
- Initial gravitating mass is informed by the data. These runs do not independently predict the observed masses, repair the HSE/lensing outliers, or simulate cluster formation and mergers.
- The work capacity and recharge history, the complete cell–orbit–bath energy and entropy account, live gas/baryon response, and a physically selected exchange rate remain open. A shared kinetic suppression rule would also need data on member galaxies/carriers rather than a hard 175 km/s switch.
- No new Lean theorem is claimed to prove an empirical success. The existing conditional conservation and dissipation results remain useful checks on the chosen rule, not a guarantee that clusters follow it.

## Files and provenance

- [Numerical tables and profiles](<C:/Users/jakef/OneDrive/Documents/Sol and Fable/02 Research/Bose contact observed clusters 2026-10-24/analysis_20261024_153135/run_summary.csv>)
- [Full machine-readable results](<C:/Users/jakef/OneDrive/Documents/Sol and Fable/02 Research/Bose contact observed clusters 2026-10-24/analysis_20261024_153135/all_results.json>)
- [Profile comparison figure](<C:/Users/jakef/OneDrive/Documents/Sol and Fable/02 Research/Bose contact observed clusters 2026-10-24/analysis_20261024_153135/cluster_profiles.png>)
- [Protocol](<C:/Users/jakef/OneDrive/Documents/Sol and Fable/02 Research/Bose contact observed clusters 2026-10-24/PROTOCOL.md>) and [numerical amendment](<C:/Users/jakef/OneDrive/Documents/Sol and Fable/02 Research/Bose contact observed clusters 2026-10-24/NUMERICAL AMENDMENT.md>)

Original X-COP data were downloaded on 23 October 2026 from the release link preserved in `Observed cluster tests 2026-10-23/source_records/xcop_allfiles.tar.gz.json`; the archive SHA256 starts 0edf5038b419b70d. MENeaCS values are the previously transcribed Herbonnet et al. (2020), arXiv:1912.04414, Table A2, with the authors’ modelling assumptions retained. `source_manifest.json` records the exact input FITS and source hashes. `source_snapshot` contains exact saved contact sources; every simulation run contains its executed adapter and numerical-gravity source.

Reproduce the accepted set by running the 21 jobs labelled final in run_final.py, all jobs in run_shared_scaling.py and run_shared_validation.py, then write_report.py. The unused later jobs in the original run_final.py queue are preserved in its audit manifest and superseded by WORK ALLOCATION AMENDMENT.md. Run prepare.py only into a fresh copy if preserving the exact prepared inputs. Simulations are not needed to read the report. All preliminary outputs are retained.
