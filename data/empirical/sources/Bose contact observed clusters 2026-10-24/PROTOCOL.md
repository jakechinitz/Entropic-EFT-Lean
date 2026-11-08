# Observed-cluster test of the Bose contact prescription

Protocol written before new cluster evolution results, 2026-10-24.

Question: does the same Bose-biased contact prescription tested on galaxies preserve the observed cluster mass distributions when its artificial dispersion gate is removed?

Data: all seven X-COP systems with released stellar profiles (A85, A1795, A2029, A2142, A2319, A644, ZW1215); the previously archived X-COP gas and hydrostatic NFW mass profiles, with the previously documented approximate stellar deprojection. Also compare the five overlapping MENeaCS NFW lensing mass estimates. These are mass reconstructions with assumptions, not raw lensing likelihoods.

First calculate the stock required by measured baryons and the reconstructed gravitating mass, and compare it with the Bose/RAR equilibrium. Then evolve particles with Claude's exact saved Bose contact kernel, three-dimensional central impulses, spherical self-gravity, and fixed measured baryons. Initialize a smooth, positive NFW stock fit to the required stock over the measured radial interval; report its fitting errors. Complete the unmeasured inner/outer profiles explicitly and construct isotropic Eddington initial conditions. The outer stock is smoothly tapered, not hard cut at R500.

Primary runs: identical initial particles with no contacts and with one or three attempts per orbit, no dispersion gate, a common initial available work of 15,000 (km/s)^2 per stock mass (the saved Milky Way value), 10 Gyr, 2,000 particles, timestep 0.5 Myr, contact interval 2 Myr. Use a shared rate and budget, with no cluster-by-cluster adjustment. If numerical controls require refinement, preserve the preliminary runs and document the reason. Start with A1795 to validate the adapter and runtime. Repeat important outcomes at finer timestep, higher particle count, or another seed. A larger common reservoir is a sensitivity test only if exhaustion is relevant. The 175 km/s gate, if applied, is a deliberately inactive control, not a theory prediction.

Diagnostics: changes in total and stock mass at fixed observed R500, radial profiles over 0.1--1 R500, late-time averages and fluctuations, accepted contacts, register balance, mechanical energy drift, instantaneous contact momentum/angular-momentum conservation, and departure from the no-contact control. Compare the measured equilibrium mismatch and the direction of evolution. Keep initial-fit error, numerical drift, and observational errors distinct; do not manufacture a joint likelihood from marginal errors.

Interpretation: this is a data-conditioned survival/stability test of an effective contact rule. The observed total mass helps set initial conditions, so preservation is not an independent mass prediction or formation calculation. The model has fixed baryons, monopole gravity, an unselected rate and work capacity, and an incomplete cell/bath energy-entropy account. It cannot establish merger lensing offsets, gas hydrostatic readjustment, three-dimensional stability, microscopic selection, or a physically derived cluster gate.

All source snapshots, preliminary outputs, and final outputs are preserved separately. Current publication files are not changed.
