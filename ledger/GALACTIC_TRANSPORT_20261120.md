# Addendum: cell count, one-cell means and stock transport (20 November 2026)

| module | content | rows |
|---|---|---|
| `Extensions20261120.CellCount` | `I k_BT_H/ħ² = g/4π² = ε` for the N.8 register inertia; `u_b/(k_BT_U) = n_nat/2`; the O.3 density as `2[u_b/(k_BT_U)] ε C`; the mean of a sum of one-cell observables over any joint law with fixed one-cell marginals is `N` times the one-cell mean | C05-91 |

C05-92 (stock transport and the lag bound) is numerical: runs of the O.3 contact dynamics with `a₀(t)` in
`02 Research/UV origin of carrier and thermal matching 2026-11-19`.
None of the 20 November results has been checked by a fresh instance.

## Correction of 21 November 2026

The transport numbers of 20 November (LAG_BY_RADIUS_2026-11-20, RULE_55) were checked under a rule written before the
check (RULE_56, VERIFICATION_OF_THE_TRANSPORT_NUMBERS_2026-11-21, `verify_results.json`). The driver reproduces a
stored run of the original selection code exactly, and every seed reruns identically. Three statements changed.

| statement of 20 November | finding | statement now |
|---|---|---|
| step times 0.29, 0.59, 0.59, 0.82, 1.05, 0.88, 1.54 Gyr (one proposal per orbit) | outside 30 kpc the estimator mixed the response with relaxation from the preparation | against a paired fixed-scale branch, eight seeds: 0.25, 0.38, 0.49, 0.89, 1.6, 3.1, 4.2 Gyr; one local orbital period from 20 to 100 kpc |
| the 0.66 Gyr bound is met inside 20 kpc because the step time is 0.59 Gyr | the bound is `a_fit = εcH(t − τ)`, an 11% excess of the fitted scale; the response is not a first-order relaxation, so a step time is not that `τ` | with `a₀ = εcH(t)` the fitted scale at `z = 0.97` equals its fixed-scale value within 1% from 10 to 50 kpc |
| outer fitted scale above `εcH` by 11, 24, 44% at 50, 100, 200 kpc | read against a reference that had not settled | from a state settled 10 Gyr: 0.5%, 9%, 30% |

Withdrawn: "inner kinematics bound the contact amplitude from below at about one proposal per orbital period". One
proposal per orbit passes with a wide margin, and the smallest passing amplitude was not run.

Not formalized: the quantum trace form `∂F/∂q = N Tr(ρ₁h)`, the slice-marginal entropy bound of H.4, the exact
diagonalizations of identical and distinguishable registers, and every transport number.
