import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Appendices K–N, field part: Misner–Sharp first integral, saddle-splay divergence, radial
divergence-free fields, x coth x ≥ 1, thermal/coherent number variances
(ledger C11-72, -73, -105; C12-04, -05, -41). -/

noncomputable section
namespace Entropic.AppKN
open Real Matrix

/-! ### Misner–Sharp first integral (C11-72, C11-73) -/

/-- C11-72: in 2D with metric h (inverse hi), gradient g = ∇R, symmetric Hessian H = ∇∇R, q = |∇R|²,
□R = tr(hi H): if the vacuum equations 2R(h□R − H) + h(q − 1) = 0 hold, then
∇_a R (1 − q) = R ∇_a q (with ∇_a q = 2(H hi g)_a), i.e. ∇M_MS = 0. -/
theorem misner_sharp_conserved (h hi Hs : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ) (R : ℝ)
    (hhi : h * hi = 1) (hsym : hiᵀ = hi) (hHs : Hsᵀ = Hs)
    (EL : ∀ a b, 2 * R * (h a b * (hi * Hs).trace - Hs a b) + h a b * (g ⬝ᵥ (hi *ᵥ g) - 1) = 0) (a : Fin 2) :
    g a * (1 - g ⬝ᵥ (hi *ᵥ g)) = R * (2 * (Hs *ᵥ (hi *ᵥ g)) a) := by
  set q := g ⬝ᵥ (hi *ᵥ g)
  set box := (hi * Hs).trace
  have htr : (hi * h).trace = 2 := by rw [mul_eq_one_comm.mp hhi]; simp
  -- trace of EL with hi
  have hT : ∑ a, ∑ b, hi b a * (2 * R * (h a b * box - Hs a b) + h a b * (q - 1)) = 0 := by
    simp [EL]
  have hbox : R * box = 1 - q := by
    have e : ∑ a, ∑ b, hi b a * (2 * R * (h a b * box - Hs a b) + h a b * (q - 1)) =
        2 * R * (box * (hi * h).trace - box) + (hi * h).trace * (q - 1) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, box]
      simp only [Fin.sum_univ_two]; ring
    rw [e, htr] at hT; linarith
  -- contraction of EL with w = hi g
  have hC : ∑ b, (2 * R * (h a b * box - Hs a b) + h a b * (q - 1)) * (hi *ᵥ g) b = 0 := by simp [EL]
  have hhw : ∑ b, h a b * (hi *ᵥ g) b = g a := by
    have := congrFun (Matrix.mulVec_mulVec g h hi) a
    rw [hhi, Matrix.one_mulVec] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have e2 : ∑ b, (2 * R * (h a b * box - Hs a b) + h a b * (q - 1)) * (hi *ᵥ g) b =
      2 * R * box * (∑ b, h a b * (hi *ᵥ g) b) - 2 * R * (Hs *ᵥ (hi *ᵥ g)) a +
        (q - 1) * ∑ b, h a b * (hi *ᵥ g) b := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e2, hhw] at hC
  have : 2 * R * box * g a = 2 * (1 - q) * g a := by rw [mul_assoc 2 R, hbox]
  linarith

/-- C11-73: M_MS = (c²R/2G)(1 − q) constant gives q = 1 − 2GM/(c²R). -/
theorem qgeo_from_mass {c G R M q : ℝ} (hc : c ≠ 0) (hR : R ≠ 0) (hG : G ≠ 0)
    (h : M = c ^ 2 * R / (2 * G) * (1 - q)) : q = 1 - 2 * G * M / (c ^ 2 * R) := by
  rw [h]; field_simp; ring

/-! ### Saddle-splay divergence (C12-05) -/

/-- C12-05: s[e] := ∂_i e^a ∂_a e^i − (div e)² equals ∂_i[(e·∇)e^i − e^i div e] pointwise, given
D_{ia} = ∂_i e^a and second derivatives S_{iab} = ∂_i∂_a e^b symmetric in (i, a). -/
theorem saddle_splay (e : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ) (S : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hS : ∀ i a b, S i a b = S a i b) :
    (∑ i, ∑ a, (D i a * D a i + e a * S i a i)) - (∑ i, (D i i * ∑ a, D a a + e i * ∑ a, S i a a)) =
      (∑ i, ∑ a, D i a * D a i) - (∑ a, D a a) ^ 2 := by
  simp only [Fin.sum_univ_three]
  rw [hS 1 0 1, hS 2 0 2, hS 0 1 0, hS 2 1 2, hS 0 2 0, hS 1 2 1]
  ring

/-! ### Radial divergence-free fields (C12-04) -/

/-- C12-04: a radial field F(r) r̂ with (r²F)′ = 0 on (0, ∞) that stays bounded near r = 0 vanishes:
r²F(r) is constant, and boundedness forces the constant to be 0. -/
theorem radial_divfree_zero (F : ℝ → ℝ) (hd : ∀ r > 0, HasDerivAt (fun s => s ^ 2 * F s) 0 r)
    (B : ℝ) (hB : ∀ r, 0 < r → r ≤ 1 → |F r| ≤ B) : ∀ r > 0, F r = 0 := by
  have hconst : ∀ r s, 0 < r → 0 < s → r ^ 2 * F r = s ^ 2 * F s := by
    intro r s hr hs
    have hcont : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt (fun s => s ^ 2 * F s) 0 (Set.Ioi 0) x :=
      fun x hx => (hd x hx).hasDerivWithinAt
    have := is_const_of_deriv_eq_zero (f := fun x => x ^ 2 * F x)
    exact (convex_Ioi (0:ℝ)).is_const_of_fderivWithin_eq_zero
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [fderivWithin_eq_fderiv (uniqueDiffOn_Ioi 0 x hx) (hd x hx).differentiableAt]
        ext; simp [(hd x hx).hasFDerivAt.fderiv]) hr hs
  intro r hr
  set C := r ^ 2 * F r
  have hsmall : ∀ s, 0 < s → s ≤ 1 → |C| ≤ s ^ 2 * B := by
    intro s hs hs1
    rw [show C = s ^ 2 * F s from hconst r s hr hs, abs_mul, abs_of_nonneg (sq_nonneg s)]
    exact mul_le_mul_of_nonneg_left (hB s hs hs1) (sq_nonneg s)
  have hC : C = 0 := by
    by_contra hne
    have hpos : 0 < |C| := abs_pos.mpr hne
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 1 one_pos le_rfl)
    set s := min 1 (Real.sqrt (|C| / (2 * (B + 1))))
    have hs : 0 < s := lt_min one_pos (Real.sqrt_pos.mpr (by positivity))
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ^ 2 ≤ |C| / (2 * (B + 1)) := by
      have : s ≤ Real.sqrt (|C| / (2 * (B + 1))) := min_le_right _ _
      calc s ^ 2 ≤ Real.sqrt (|C| / (2 * (B + 1))) ^ 2 := by gcongr
        _ = |C| / (2 * (B + 1)) := Real.sq_sqrt (by positivity)
    have := hsmall s hs hs1
    have : s ^ 2 * B ≤ |C| / (2 * (B + 1)) * B := mul_le_mul_of_nonneg_right hs2 hB0
    have : |C| / (2 * (B + 1)) * B < |C| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hr2 : r ^ 2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp hC).resolve_left hr2

/-! ### x coth x ≥ 1 (C12-41) -/

/-- C12-41: for x > 0, x cosh x ≥ sinh x (equivalently x coth x ≥ 1). -/
theorem x_coth_ge_one {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  let f : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
  have hf : ∀ t, HasDerivAt f (t * Real.sinh t) t := by
    intro t
    have := ((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
    convert this using 1; ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t _ => (hf t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hf t).deriv]
      exact mul_nonneg (le_of_lt ht) (Real.sinh_nonneg_iff.mpr (le_of_lt ht))
  have := hmono (Set.mem_Ici.mpr le_rfl) hx hx
  simp [f] at this
  linarith

/-! ### Thermal and coherent number variances (C11-105) -/

/-- C11-105 (thermal): for P(N) = (1 − r)rᴺ with mean N̄ = r/(1 − r), ⟨N(N−1)⟩ = 2r²/(1 − r)² so
Var N = N̄(1 + N̄). -/
theorem thermal_variance {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    let Nb := r / (1 - r)
    2 * r ^ 2 / (1 - r) ^ 2 + Nb - Nb ^ 2 = Nb * (1 + Nb) := by
  intro Nb
  have : (1 - r) ≠ 0 := by linarith
  simp only [Nb]; field_simp; ring

/-- C11-105 (coherent): a Poisson number law has ⟨N(N−1)⟩ = N̄², so Var N = N̄; hence
Var(c₀N) = c₀²N̄(1 + N̄) (thermal) and c₀²N̄ (coherent). -/
theorem coherent_variance (Nb c0 : ℝ) : Nb ^ 2 + Nb - Nb ^ 2 = Nb ∧ c0 ^ 2 * (Nb * (1 + Nb)) = c0 ^ 2 * Nb * (1 + Nb) := by
  constructor <;> ring

end Entropic.AppKN
