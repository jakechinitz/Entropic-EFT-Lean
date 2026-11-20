import Mathlib

/-!
# Response ladders: Unruh ratio and bulk-equipartition counts (Appendices N.8, O.3)

* `unruh_ratio`: with `k_B T_U = ħ g_b/(2πc)`, `k_B T_H = ħH/(2π)`, `a₀ = ε c H` and `g_b = x² a₀`,
  `T_U/T_H = ε x²`. The harmonic requirement `N ε x² ≳ 2.5` of N.8 is therefore `N k_B T_U ≳ 2.5 k_B T_H`.
* `ladders_per_nat`: counting degrees of freedom by bulk equipartition, `E/(½ k_B T)`, the mutual field
  `E_mut = n(1+n) g_b²/(8πG)` at `T_H` against the baryonic field `E_b = g_b²/(8πG)` at `T_U` gives
  `n(1+n) ε x²` ladders per displaced nat, the O.3 density `ε C_E(x)`.

The numerical threshold 2.5 and the SPARC bounds on the locked-group size are not formalized.
-/

noncomputable section
namespace Entropic.Extensions20261119.Ladders
open Real

theorem unruh_ratio (ħ c H ε x : ℝ) (hħ : 0 < ħ) (hc : 0 < c) (hH : 0 < H) :
    (ħ * (x ^ 2 * (ε * c * H)) / (2 * π * c)) / (ħ * H / (2 * π)) = ε * x ^ 2 := by
  have hπ : 0 < π := Real.pi_pos
  field_simp

theorem ladders_per_nat (n gb G kTH kTU ε x : ℝ) (hg : 0 < gb) (hG : 0 < G) (hH : 0 < kTH) (hU : 0 < kTU)
    (hr : kTU / kTH = ε * x ^ 2) :
    ((n * (1 + n) * gb ^ 2 / (8 * π * G)) / (kTH / 2)) / ((gb ^ 2 / (8 * π * G)) / (kTU / 2))
      = n * (1 + n) * (ε * x ^ 2) := by
  have hπ : 0 < π := Real.pi_pos
  rw [← hr]
  field_simp

end Entropic.Extensions20261119.Ladders
