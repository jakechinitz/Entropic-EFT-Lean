# Diamond-lattice Green function G_tet(0) (2026-10-27)

Module group `Entropic/DiamondGreen` (six files, imported by `Entropic.lean`). No `sorry`, no
custom axioms, no `native_decide`; every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`. Lean 4.35.0, mathlib v4.35.0 (pins unchanged).

## Proved unconditionally

| Lean name (namespace `Entropic.DiamondGreen`) | Statement |
|---|---|
| `greenDiamond_eq_integral` | the manuscript's integral (2π)⁻³ ∫_{[-π,π]³} 4 d³k / (16 − \|1 + e^{ik₁} + e^{ik₂} + e^{ik₃}\|²) equals the Neumann series ∑_L (A^L)₀₀ / 4^(L+1) of [(4 − A)⁻¹]₀₀ |
| `integral_normSq_pow` | (2π)⁻³ ∫ \|λ(k)\|^{2n} = number of closed diamond walks of length 2n |
| `dWalks_even` | closed diamond walks of length 2n from A_y to A_x = ∑_k C(n,k) 4^(n−k) · fcc walks of length k from y to x |
| `dWalks_odd` | odd A→A walks vanish |
| `greenDiamond_eq` | G_tet(0) = P_fcc / 3, P_fcc = ∑_k w_k^fcc / 12^k the expected number of returns of the fcc random walk |
| `greenDiamond_lt_top` | G_tet(0) < ∞ (transience of the diamond lattice): 16 − \|λ\|² ≥ (4/π²)\|k\|² on the cube, and 1/\|k\|² ≤ (1/3)∏\|kᵢ\|^(−2/3) by AM–GM |
| `Gtet0_ge` | G_tet(0) ≥ 1/4 |
| `returnFCC_eq_integral` | P_fcc = (2π)⁻³ ∫ 12 / (12 − ∑_v cos(k·v)) (fcc Brillouin-zone integral, primitive coordinates) |
| `watsonAGM_bounds` | 0.44822039438838 < √3 / (4 agm(1, cos 15°)²) < 0.44822039438839 (mathlib `NNReal.agm`, three AGM steps) |
| `dWalks_small`, `dWalks_eight`, `fWalks_small` | Domb numbers 1, 4, 28, 256 by enumeration and 2716 through the reduction; fcc return counts 1, 0, 12, 48, 540 |

## Proved given the cited input `WatsonFCC`

| Lean name | Statement |
|---|---|
| `manuscript_Gtet` | the manuscript integral equals √3/(4 agm(1, cos 15°)²) and lies in (0.44822039438838, 0.44822039438839) |
| `Gtet0_bounds` | the same bracket for the real number G_tet(0) |
| `SInfCell_bounds` | 0.0461482515 < S₀ = 3 ln 2 / (32π G_tet(0)) < 0.0461482516 |
| `source_amplitude_bounds` | 0.1094722281 < ln(7/6) / (π G_tet(0)) < 0.1094722285 |

## The cited input

`WatsonFCC`: (2π)⁻³ ∫_{[-π,π]³} 12 / (12 − ∑_v cos(k·v)) d³k = 3 · √3 / (4 agm(1, cos 15°)²), the fcc
lattice Green function in primitive coordinates. It packages three classical facts:

1. the lattice change of basis from primitive to Cartesian coordinates, which turns the left side into
   3 × Watson's triple integral (2π)⁻³ ∫ d³k / (3 − cos k₁ cos k₂ − cos k₂ cos k₃ − cos k₃ cos k₁);
2. Watson's evaluation of that integral as 3Γ(1/3)⁶ / (2^(14/3) π⁴) (G. N. Watson, Q. J. Math. 10
   (1939) 266);
3. Legendre's singular value K(sin 15°) = 3^(1/4) Γ(1/3)³ / (2^(7/3) π) and Gauss's
   K(k) = π / (2 agm(1, k')), which rewrite the Γ form as the AGM form.

It is a hypothesis of the theorems that use it, not an axiom. Finiteness of G_tet(0) and the
fcc Fourier representation are proved and are not part of it. The Γ form of Joyce's value occurs
only in documentation; the Lean statements use the AGM form.

## Independent checks (review of 2026-10-27)

A separate reviewer, working from the files alone, recomputed: Watson's integral by one analytic and
two numerical integrations, 0.44822039438838141, so 3W = 1.3446611831651442 (fcc return probability
0.256318); the AGM form, agreeing to about 2e-17; the Γ form against the AGM form, agreeing to 1e-31;
the manuscript integral directly, 0.44822039438838143; the fcc return counts 1, 0, 12, 48, 540, 4320,
42240 and the Domb numbers 1, 4, 28, 256, 2716, 31504 by brute force with the Lean neighbour lists.
The review found the statements faithful and asked that the bundling in `WatsonFCC` be stated
explicitly and that finiteness not rest on it; both are done above.

## Ledger rows

- C05-20 proved (`greenDiamond_eq_integral`).
- C05-21, C05-22, C05-25, C05-29, C11-12, C11-13 proved given `WatsonFCC`.
- C05-11 (point-source response as an ℓ² inverse) is unchanged.

## Scope

The theorems concern the diamond graph and its Green function as defined in Appendix C.5. They do
not bear on whether that graph is the right coarse adjacency of the tetrahedral boundary complex,
which the manuscript adopts as a modelling choice.
