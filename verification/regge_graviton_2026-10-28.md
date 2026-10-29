# Regge graviton: linearized Regge calculus → linearized Einstein gravity (2026-10-28)

Module group `Entropic/ReggeGraviton` (sixteen modules, Lean 4.35.0, mathlib v4.35.0). No `sorry`, no
custom axioms, no `native_decide`. The 1,025 moment identities are checked by kernel `decide`.

## Setting

The hypercubic lattice `ℤ⁴`, each unit hypercube cut into the 24 path simplices
`0 → e_{π1} → e_{π1}+e_{π2} → e_{π1}+e_{π2}+e_{π3} → (1,1,1,1)` (Freudenthal–Kuhn). This is the
subdivision used for the length-Regge reference case in Dittrich et al., arXiv:2105.10808, who
attribute the length-Regge Hessian on it to Roček and Williams. Variables: the 15 squared edge lengths
per vertex. Action: `∑_t A_t ε_t` to second order about flat Euclidean space.

Appendix H.10 cites its symbol from Dittrich–Kogios for the centrally subdivided lattice. This work
computes the symbol on a different regular lattice. It replaces the cited input for the regular
metric-Regge branch; it does not reproduce the cited lattice.

## What is proved

| Lean name (namespace `Entropic.ReggeGraviton`) | Statement |
|---|---|
| `simplexData_kuhn` | the edge table is the Freudenthal–Kuhn triangulation |
| `KC_eq`, `Cm_eq` | the body-diagonal block of the lattice Hessian is `−½ I` at every momentum |
| `Kred_schur` | the reduced kernel is the Schur complement `A − B C⁻¹ B†` (body diagonals integrated out) |
| `Kred_herm` | it is Hermitian for every momentum |
| `symbol_limit` | `ε⁻² Kred(εk) → KEH(k)` for every `k` and every entry |
| `KEH_quad` | `KEH` is the Fourier kernel of `(√g R)⁽²⁾` (Fierz–Pauli form) |
| `KEHg_TT` | in Frobenius-normalized coordinates, transverse-traceless polarizations are an eigenspace of the continuum operator with eigenvalue `−¼\|k\|²` |
| `strong_resolvent_conv` | generic: pointwise-convergent Hermitian matrix symbols give strong-resolvent convergence of the multiplication operators on `L²(ℝ⁴; ℂⁿ)`, with exhausting cutoffs |
| `regge_strong_resolvent_normalized` | for `Im z ≠ 0`, `f ∈ L²(ℝ⁴; ℂ¹⁰)`: the Frobenius-normalized lattice operators on `BZ_a = [−π/a, π/a]⁴` converge to the linearized Einstein operator in the strong-resolvent sense as `a → 0⁺` |

Consequences: `∑_t A_t ε_t = ½∫√g R` at quadratic order on this lattice, with coefficient exactly 1.
The Euclidean Regge action `−(1/8πG)∑_t A_t ε_t` gives `(1/64πG)|k|²|h|²` per transverse-traceless
mode (with `∫d⁴k/(2π)⁴` normalization): a two-derivative, massless, spin-2 kernel.

## The one input not derived in Lean

`hzL`: 48 × the flat Hessian of the Regge action of one Kuhn 4-simplex in squared edge lengths,
computed in exact rational arithmetic from the dihedral-angle derivatives through the Schläfli
identity (`tools/regge_simplex_hessian.py`). The metric placement at edge midpoints and the map
`δs_v = v^μ v^ν h_μν` are definitions.

## Independent checks

My own:
- `tools/regge_exact_series.py`, rational arithmetic with symbolic momentum: orders `ε⁰`, `ε¹` and `ε³`
  vanish, and order `ε²` equals `KEH` exactly. So `Kred(εk) = ε² KEH(k) + O(ε⁴)`, the rate stated in
  H.10. This rate is checked in Python, not in Lean.

A separate reviewer, working from the files alone, found:
- **Hessian.** On a 4⁴ torus (6,144 simplices), finite-difference second derivatives of the true
  action (dihedral angles from vertex coordinates, not the Schläfli route) match the assembled
  `hzL` quadratic form to about 1e-8. The hyper-diagonal second derivative vanishes.
- **Kernel and coefficient.** A sympy expansion of `√g R` reproduces `½ FP` exactly. A real-space torus
  check gives the action ratio `1.102`, `1.046` at `L = 8`, `12`, tending to 1 as `k²`.
- **Spectrum.** Over 20,000 random momenta and all Brillouin-zone corners, the reduced kernel has
  exactly 4 zero modes (the lattice diffeomorphisms), 5 negative modes and 1 positive (conformal)
  mode. The smallest non-gauge `|eigenvalue|` is at least `0.058 |q|²`, so there are no doublers.
  This is numerical; the resolvent theorem itself cannot detect doublers.
- **Statement.** The review caught that the first version of the resolvent theorem used the plain
  inner product on the coordinates, in which transverse-traceless modes are not an eigenspace.
  The Frobenius-normalized statement and `KEHg_TT` were added in response.

## Manuscript claims affected

- C08-61: proved in Euclidean four-dimensional form for the Freudenthal–Kuhn regular branch.
- C07-115: proved at quadratic order on that regular lattice.
- C08-63: partial (TT eigenvalue).
- C08-62 (functional calculus for `H = c√(K/Z_G)`): not formalized.

## Scope and caveats

- The theory is quadratic (free) about flat Euclidean space on one regular lattice. There is no
  interacting theory, no irregular or dynamical triangulation (the CDT host), and no Lorentzian
  continuation or reflection positivity.
- In Euclidean 4D, `P_TT` has rank 5; the Lorentzian spatial TT sector has 2 helicities.
- The positive conformal mode makes the Euclidean action unbounded below (the conformal-factor
  problem).
- The hyper-diagonal edge is an exact zero mode at every momentum, beyond the four diffeomorphisms.
  It drops out of the metric kernel, but a lattice path integral would have to fix it.
- The selection of the metric-Regge branch from the capacity microstructure remains a premise
  (H.9a).
