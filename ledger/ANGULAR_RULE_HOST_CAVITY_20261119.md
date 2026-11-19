# Angular rule, host couplings and cavity ensemble: manuscript and formalization map

The full manuscript of 19 November 2026 adds to Q.11 the statement that the full-turn rule follows from
invariance of the weight under flat subdivision; to J.12, the count content of the host couplings; to J.14 and
Section 24.10, the volume dependence of the published bifurcation line. The cavity ensemble of F.5 was added on
18 November. `Entropic/Extensions20261119/` formalizes the mathematical statements.

| Module | What is proved | Ledger |
|---|---|---|
| `AngularRule` | a positive continuous wedge factor `k` with `k(θ₁+θ₂) = k(θ₁)k(θ₂)` and `2k(2π) = 1` is `e^{−θ ln2/(2π)}`; any other amplitude gives a flat hinge log-weight `ln 2 − 2πb' ≠ 0`; the hinge weight `2e^{−b(2π−δ)} = e^{bδ}` is exactly linear in `δ`; `bFlat = AppQ.bH` | C03-44, C15-50 |
| `HostCount` | with `N₂^SL = N₄₁`, `N₂^TL = 2N₀ + N₄₁ + 2N₃₂`, the hinge traces fix `κ₀ + 6Δ = 2r ln 2` for every per-simplex factor; `Δ = ln2[(r−1) − (b'/b)(S₃₂ − S₄₁)]`; a centring term shifts `(κ₀, Δ, κ₄)` by `(3x, −x/2, x/2)`; `6 ln 2` at `α = 7` | C03-44, C10-115 |
| `Cavity` | `F(τ,x) = τ(1 − √(1−x)) − x²`: nonnegative at `τ = 32/27` with zeros `x = 0, 8/9`; gas wins above, cap wins below; `T_c r_B = 27/(32π)`; jump `64/81`; stationary caps only for `τ ≤ 8√3/9`; `T_H/(1 − γ/ln 2) = T_H` iff `γ = 0` | C05-84, C05-85 |

Inputs that the Lean takes as given:

- that a wedge acts on a half-bond as a scalar of its angle alone (port-number conservation, occupation exchange, the
  lattice Bisognano–Wichmann property of the bond vacuum);
- the counting identities of closed causal triangulations of `S¹ × S³` (Dehn–Sommerville; checked on twenty
  triangulations in `02 Research/Einstein weight as a count 2026-11-18`) and the coverage sums `S₄₁ = 4.5013`,
  `S₃₂ = 6.0308` from the dihedral angles at `α = 7`;
- the reduced cavity weight of the two fillings of `S¹ × S²` (`02 Research/Black hole transfer audit 2026-11-18`).

Not formalized: the greybody and line-width numerics of F.6, the environment estimates, and the volume dependence of
the bifurcation line (C10-116, data).
