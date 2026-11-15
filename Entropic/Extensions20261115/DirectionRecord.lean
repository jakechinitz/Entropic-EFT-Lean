import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Entropic.AppIJ.Color

/-!
# Direction records and the Wilson operator (Appendix I.9)

On the diamond bonds `n_j` (`Entropic.AppIJ.tet` in units of `1/√3`) write `z_j = e^{ik·n_j}` for the four
port phases of a Bloch wave. The paragraph "Direction records and the Wilson operator" of I.9 states

* `W = (3/2)|V|² = 8(1 − |f|²/16)` for `f = Σ_j z_j`, `V = Σ_j n_j z_j`,
  `W = Σ_{j<l}[1 − cos(k·(n_j − n_l))]` (`wilson_eq_port`, `wilson_eq_direction`, `wilson_cos`);
* `W/8` is the squared projection of the normalized port vector `z_j/2` on the complement of the
  symmetric port state (`direction_weight`);
* the nearest-neighbour hop is `Q = −it σ·V` (`hop_eq_sigma_dot`), with `det Q = t² V·V` (`hop_det`);
* the direction component has weight `O(k²)` at long wavelength (`wilson_le_sq`) and vanishes at zero
  momentum (`wilson_zero`);
* the sum over cells of the complement projectors has Bloch symbol `W/2` (`record_symbol`), so that
  independent renewals of rate `λ` erasing a record of strength `s` give the decay generator
  `λ s Σ_b D_b` with symbol `(λ s/2) W` (`decay_generator`, `decay_symbol`) and coefficient
  `γ_W = (d/4L_*) s` in bond units (`gammaW_eq`).

What is not formalized: the identification of this amplitude damping with the Hermitian Wilson mass term
(a many-body statement the manuscript leaves open) and the record assignment of the five-edge improvement.
-/

noncomputable section
namespace Entropic.Extensions20261115.DirectionRecord
open Entropic.AppIJ
open scoped ComplexConjugate

/-- Port amplitude `f = Σ_j z_j`. -/
def portSum (z : Fin 4 → ℂ) : ℂ := ∑ j, z j

/-- Direction vector in units of `1/√3`: `U_c = Σ_j tet j c · z_j = √3 V_c`. -/
def dirVec (z : Fin 4 → ℂ) (c : Fin 3) : ℂ := ∑ j, (tet j c : ℂ) * z j

/-- `|V|² = (1/3) Σ_c |U_c|²`. -/
def dirNormSq (z : Fin 4 → ℂ) : ℝ := (1/3) * ∑ c, Complex.normSq (dirVec z c)

/-- Wilson function `W = Σ_{j<l} [1 − Re(z_j z̄_l)]`. -/
def wilson (z : Fin 4 → ℂ) : ℝ :=
  ∑ j : Fin 4, ∑ l : Fin 4, if j < l then 1 - (z j * conj (z l)).re else 0

/-- Tetrahedral identity `n_j·n_l = −1/3` for `j ≠ l` and `1` for `j = l`, in units where `|n|² = 3`. -/
theorem tet_dot (j l : Fin 4) : ∑ c, tet j c * tet l c = if j = l then 3 else -1 := by
  revert j l; decide

/-- The bonds sum to zero. -/
theorem tet_sum (c : Fin 3) : ∑ j, tet j c = 0 := by
  revert c; decide

private theorem unit_re_im {w : ℂ} (h : Complex.normSq w = 1) : w.re * w.re + w.im * w.im = 1 := by
  rwa [Complex.normSq_apply] at h

/-- For phases `z_j = e^{iθ_j}` the Wilson function is `Σ_{j<l}[1 − cos(θ_j − θ_l)]`. -/
theorem wilson_cos (θ : Fin 4 → ℝ) :
    wilson (fun j => Complex.exp (θ j * Complex.I)) =
      ∑ j : Fin 4, ∑ l : Fin 4, if j < l then 1 - Real.cos (θ j - θ l) else 0 := by
  unfold wilson
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have e : Complex.exp (θ j * Complex.I) * conj (Complex.exp (θ l * Complex.I)) =
      Complex.exp (((θ j - θ l : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
    ring
  simp only [e, Complex.exp_ofReal_mul_I_re]

/-- I.9: `W = 8(1 − |f|²/16)`. -/
theorem wilson_eq_port (z : Fin 4 → ℂ) (h : ∀ j, Complex.normSq (z j) = 1) :
    wilson z = 8 * (1 - Complex.normSq (portSum z) / 16) := by
  have h0 := unit_re_im (h 0); have h1 := unit_re_im (h 1)
  have h2 := unit_re_im (h 2); have h3 := unit_re_im (h 3)
  simp only [wilson, portSum, Fin.sum_univ_four, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [show ((0 : Fin 4) < 1) = True from by decide, show ((0 : Fin 4) < 2) = True from by decide,
    show ((0 : Fin 4) < 3) = True from by decide, show ((1 : Fin 4) < 2) = True from by decide,
    show ((1 : Fin 4) < 3) = True from by decide, show ((2 : Fin 4) < 3) = True from by decide,
    show ((0 : Fin 4) < 0) = False from by decide, show ((1 : Fin 4) < 0) = False from by decide,
    show ((1 : Fin 4) < 1) = False from by decide, show ((2 : Fin 4) < 0) = False from by decide,
    show ((2 : Fin 4) < 1) = False from by decide, show ((2 : Fin 4) < 2) = False from by decide,
    show ((3 : Fin 4) < 0) = False from by decide, show ((3 : Fin 4) < 1) = False from by decide,
    show ((3 : Fin 4) < 2) = False from by decide, show ((3 : Fin 4) < 3) = False from by decide,
    ite_true, ite_false]
  linear_combination (1/2) * (h0 + h1 + h2 + h3)

private theorem lt_simp :
    ((0 : Fin 4) < 1) = True ∧ ((0 : Fin 4) < 2) = True ∧ ((0 : Fin 4) < 3) = True ∧
    ((1 : Fin 4) < 2) = True ∧ ((1 : Fin 4) < 3) = True ∧ ((2 : Fin 4) < 3) = True ∧
    ((0 : Fin 4) < 0) = False ∧ ((1 : Fin 4) < 0) = False ∧ ((1 : Fin 4) < 1) = False ∧
    ((2 : Fin 4) < 0) = False ∧ ((2 : Fin 4) < 1) = False ∧ ((2 : Fin 4) < 2) = False ∧
    ((3 : Fin 4) < 0) = False ∧ ((3 : Fin 4) < 1) = False ∧ ((3 : Fin 4) < 2) = False ∧
    ((3 : Fin 4) < 3) = False := by decide

/-- The six pair terms of the Wilson function. -/
theorem wilson_pairs (z : Fin 4 → ℂ) :
    wilson z = (1 - (z 0 * conj (z 1)).re) + (1 - (z 0 * conj (z 2)).re) + (1 - (z 0 * conj (z 3)).re) +
      (1 - (z 1 * conj (z 2)).re) + (1 - (z 1 * conj (z 3)).re) + (1 - (z 2 * conj (z 3)).re) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := lt_simp
  simp only [wilson, Fin.sum_univ_four, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
    ite_true, ite_false]
  ring

private theorem dirVec0 (z : Fin 4 → ℂ) : dirVec z 0 = z 0 + z 1 - z 2 - z 3 := by
  simp [dirVec, tet, Fin.sum_univ_four]; ring
private theorem dirVec1 (z : Fin 4 → ℂ) : dirVec z 1 = z 0 - z 1 + z 2 - z 3 := by
  simp [dirVec, tet, Fin.sum_univ_four]; ring
private theorem dirVec2 (z : Fin 4 → ℂ) : dirVec z 2 = z 0 - z 1 - z 2 + z 3 := by
  simp [dirVec, tet, Fin.sum_univ_four]; ring

/-- I.9: `W = (3/2)|V|²`. -/
theorem wilson_eq_direction (z : Fin 4 → ℂ) (h : ∀ j, Complex.normSq (z j) = 1) :
    wilson z = (3/2) * dirNormSq z := by
  have h0 := unit_re_im (h 0); have h1 := unit_re_im (h 1)
  have h2 := unit_re_im (h 2); have h3 := unit_re_im (h 3)
  rw [wilson_pairs]
  simp only [dirNormSq, Fin.sum_univ_three, dirVec0, dirVec1, dirVec2, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  linear_combination (-3/2) * (h0 + h1 + h2 + h3)

/-- I.9, both forms together: `W = (3/2)|V|² = 8(1 − |f|²/16)`. -/
theorem wilson_identity (z : Fin 4 → ℂ) (h : ∀ j, Complex.normSq (z j) = 1) :
    wilson z = (3/2) * dirNormSq z ∧ (3/2) * dirNormSq z = 8 * (1 - Complex.normSq (portSum z) / 16) :=
  ⟨wilson_eq_direction z h, by rw [← wilson_eq_direction z h, wilson_eq_port z h]⟩

/-- `|f|² + 3|V|² = 16`: the symmetric and direction weights of the four port phases add to four,
`|f|²/4 + (3/4)|V|² = 4`. -/
theorem port_direction_split (z : Fin 4 → ℂ) (h : ∀ j, Complex.normSq (z j) = 1) :
    Complex.normSq (portSum z) + 3 * dirNormSq z = 16 := by
  have := (wilson_identity z h).2; linarith

/-- I.9: for the normalized port vector `ψ_j = z_j/2`, the component orthogonal to the symmetric port
state `u = (1/2, 1/2, 1/2, 1/2)` is `ψ_j − f/8`, and its squared norm is `W/8`. -/
theorem direction_weight (z : Fin 4 → ℂ) (h : ∀ j, Complex.normSq (z j) = 1) :
    ∑ j, Complex.normSq (((1/2 : ℝ) : ℂ) * z j - ((1/8 : ℝ) : ℂ) * portSum z) = wilson z / 8 := by
  have h0 := unit_re_im (h 0); have h1 := unit_re_im (h 1)
  have h2 := unit_re_im (h 2); have h3 := unit_re_im (h 3)
  rw [wilson_eq_port z h]
  simp only [portSum, Fin.sum_univ_four, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  linear_combination (1/4) * (h0 + h1 + h2 + h3)

/-- At zero momentum (`z_j = 1`) only the symmetric component is present. -/
theorem wilson_zero : wilson (fun _ => 1) = 0 ∧ Complex.normSq (portSum fun _ => 1) = 16 ∧
    dirNormSq (fun _ => 1) = 0 := by
  have hp : Complex.normSq (portSum fun _ => 1) = 16 := by
    simp [portSum]; norm_num
  have hw := wilson_identity (fun _ => (1 : ℂ)) (fun _ => by simp)
  refine ⟨by rw [hw.1, hw.2, hp]; norm_num, hp, ?_⟩
  have := hw.2; rw [hp] at this; linarith

/-! ### Long wavelength -/

/-- Bond phase `θ_j = k·n_j = Σ_c tet j c · κ_c` with `κ = k/√3`. -/
def phase (κ : Fin 3 → ℝ) (j : Fin 4) : ℝ := ∑ c, (tet j c : ℝ) * κ c

private theorem phase_vals (κ : Fin 3 → ℝ) :
    phase κ 0 = κ 0 + κ 1 + κ 2 ∧ phase κ 1 = κ 0 - κ 1 - κ 2 ∧ phase κ 2 = -κ 0 + κ 1 - κ 2 ∧
      phase κ 3 = -κ 0 - κ 1 + κ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [phase, tet, Fin.sum_univ_three] <;> ring

/-- I.9, long wavelength: `W(k) ≤ 8|κ|² = (8/3)|k|²`, so the direction component has weight `O(k²)`. -/
theorem wilson_le_sq (κ : Fin 3 → ℝ) :
    wilson (fun j => Complex.exp (phase κ j * Complex.I)) ≤ 8 * (κ 0 ^ 2 + κ 1 ^ 2 + κ 2 ^ 2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := lt_simp
  obtain ⟨p0, p1, p2, p3⟩ := phase_vals κ
  rw [wilson_cos]
  simp only [Fin.sum_univ_four, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10,
    ite_true, ite_false]
  have key : ∀ x : ℝ, 1 - Real.cos x ≤ x ^ 2 / 2 := fun x => by
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have k01 := key (phase κ 0 - phase κ 1); have k02 := key (phase κ 0 - phase κ 2)
  have k03 := key (phase κ 0 - phase κ 3); have k12 := key (phase κ 1 - phase κ 2)
  have k13 := key (phase κ 1 - phase κ 3); have k23 := key (phase κ 2 - phase κ 3)
  have hsum : (phase κ 0 - phase κ 1) ^ 2 / 2 + (phase κ 0 - phase κ 2) ^ 2 / 2 +
      (phase κ 0 - phase κ 3) ^ 2 / 2 + (phase κ 1 - phase κ 2) ^ 2 / 2 +
      (phase κ 1 - phase κ 3) ^ 2 / 2 + (phase κ 2 - phase κ 3) ^ 2 / 2 =
        8 * (κ 0 ^ 2 + κ 1 ^ 2 + κ 2 ^ 2) := by
    rw [p0, p1, p2, p3]; ring
  linarith

/-! ### The hop -/

/-- Pauli matrices. -/
def σ : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- `σ·U` for a complex three-vector. -/
def pauliDot (U : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ∑ c, U c • σ c

/-- Spin transport on bond `j` in units of `1/√3`: `√3 S_j = −i (√3 n_j)·σ`. -/
def bondSpin (j : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := (-Complex.I) • pauliDot (fun c => (tet j c : ℂ))

/-- I.9: `Σ_j z_j S_j = −i σ·V` (both sides in units of `1/√3`; multiply by `t` for `Q`). -/
theorem hop_eq_sigma_dot (z : Fin 4 → ℂ) :
    ∑ j, z j • bondSpin j = (-Complex.I) • pauliDot (dirVec z) := by
  simp only [bondSpin, pauliDot, dirVec, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1; ring

/-- `det(σ·U) = −U·U` with the bilinear product. -/
theorem pauliDot_det (U : Fin 3 → ℂ) :
    (pauliDot U).det = -(U 0 ^ 2 + U 1 ^ 2 + U 2 ^ 2) := by
  simp [pauliDot, σ, Fin.sum_univ_three, Matrix.det_fin_two]
  ring_nf
  rw [Complex.I_sq]; ring

/-- `det(−it σ·V) = t² V·V`; in units of `1/√3`, `det(−i σ·U) = U·U`. The plain hop is singular exactly
where the bilinear square of the direction vector vanishes. -/
theorem hop_det (z : Fin 4 → ℂ) :
    ((-Complex.I) • pauliDot (dirVec z)).det = dirVec z 0 ^ 2 + dirVec z 1 ^ 2 + dirVec z 2 ^ 2 := by
  rw [Matrix.det_smul, pauliDot_det]
  simp only [Fintype.card_fin]
  rw [show (-Complex.I) ^ 2 = -1 by rw [neg_sq, Complex.I_sq]]; ring

/-! ### The record operator and its Bloch symbol -/

/-- Symmetric projection at cell `b`: the average of the amplitudes on its four neighbours `b − n_l`. -/
def cellAvg (ψ : (Fin 3 → ℤ) → ℂ) (b : Fin 3 → ℤ) : ℂ := (1/4 : ℂ) * ∑ l, ψ (b - tet l)

/-- `(Σ_b D_b ψ)(x)`: the site `x` is a neighbour of the four cells `x + n_j`, and `D_b = I − P_b` on the
four neighbours of `b`. -/
def recordOp (ψ : (Fin 3 → ℤ) → ℂ) (x : Fin 3 → ℤ) : ℂ := ∑ j, (ψ x - cellAvg ψ (x + tet j))

private theorem char_zero' {χ : (Fin 3 → ℤ) → ℂ} (hmul : ∀ x y, χ (x + y) = χ x * χ y)
    (hunit : ∀ x, Complex.normSq (χ x) = 1) : χ 0 = 1 := by
  have h := hmul 0 0; rw [add_zero] at h
  have hne : χ 0 ≠ 0 := fun h0 => by have := hunit 0; rw [h0] at this; simp at this
  exact (mul_right_cancel₀ hne (by rw [one_mul]; exact h)).symm

private theorem char_neg {χ : (Fin 3 → ℤ) → ℂ} (hmul : ∀ x y, χ (x + y) = χ x * χ y)
    (hunit : ∀ x, Complex.normSq (χ x) = 1) (y : Fin 3 → ℤ) : χ (-y) = conj (χ y) := by
  have h := hmul (-y) y; rw [neg_add_cancel, char_zero' hmul hunit] at h
  have hc : χ y * conj (χ y) = 1 := by rw [Complex.mul_conj, hunit y]; simp
  calc χ (-y) = χ (-y) * (χ y * conj (χ y)) := by rw [hc, mul_one]
    _ = (χ (-y) * χ y) * conj (χ y) := by ring
    _ = conj (χ y) := by rw [← h, one_mul]

/-- I.9: on a Bloch wave (a unit character `χ` of the lattice) the record operator `Σ_b D_b` acts as
multiplication by `W(k)/2`, with port phases `z_j = χ(n_j)`. -/
theorem record_symbol (χ : (Fin 3 → ℤ) → ℂ) (hmul : ∀ x y, χ (x + y) = χ x * χ y)
    (hunit : ∀ x, Complex.normSq (χ x) = 1) (x : Fin 3 → ℤ) :
    recordOp χ x = ((wilson (fun j => χ (tet j)) / 2 : ℝ) : ℂ) * χ x := by
  have hstep : ∀ j l : Fin 4, χ (x + tet j - tet l) = χ x * χ (tet j) * conj (χ (tet l)) := fun j l => by
    rw [sub_eq_add_neg, hmul, hmul, char_neg hmul hunit]
  have hW := wilson_eq_port (fun j => χ (tet j)) (fun j => hunit _)
  have hf : ((Complex.normSq (portSum fun j => χ (tet j)) : ℝ) : ℂ) =
      (∑ j, χ (tet j)) * conj (∑ l, χ (tet l)) := by
    rw [Complex.mul_conj]; rfl
  rw [hW]
  simp only [recordOp, cellAvg, hstep]
  push_cast
  rw [hf, map_sum]
  simp only [Fin.sum_univ_four]
  ring

/-- I.9: a renewal of cell `b` multiplies the direction component by `1 − s` and leaves the symmetric
component: `(1 − s)(ψ − Pψ) + Pψ = ψ − s(ψ − Pψ)`. -/
theorem renewal_step (s a avg : ℂ) : (1 - s) * (a - avg) + avg = a - s * (a - avg) := by ring

/-- I.9: independent renewals of the four cells adjacent to `x`, each at rate `lam`, change `ψ(x)` at the
rate `−lam·s·(Σ_b D_b ψ)(x)`. -/
theorem decay_generator (lam s : ℂ) (ψ : (Fin 3 → ℤ) → ℂ) (x : Fin 3 → ℤ) :
    ∑ j, lam * ((ψ x - s * (ψ x - cellAvg ψ (x + tet j))) - ψ x) = -(lam * s) * recordOp ψ x := by
  simp only [recordOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- I.9: on a Bloch wave the decay generator is multiplication by `−(lam·s/2) W(k)`. -/
theorem decay_symbol (lam s : ℝ) (χ : (Fin 3 → ℤ) → ℂ) (hmul : ∀ x y, χ (x + y) = χ x * χ y)
    (hunit : ∀ x, Complex.normSq (χ x) = 1) (x : Fin 3 → ℤ) :
    ∑ j, (lam : ℂ) * ((χ x - (s : ℂ) * (χ x - cellAvg χ (x + tet j))) - χ x) =
      ((-(lam * s / 2 * wilson fun j => χ (tet j)) : ℝ) : ℂ) * χ x := by
  rw [decay_generator, record_symbol χ hmul hunit]
  push_cast; ring

/-- I.9: with renewal rate `λ = c/(2L_*)` per cell and bond length `d`, the coefficient of `W` in bond
units is `γ_W = (λ d/2c) s = (d/4L_*) s`. -/
theorem gammaW_eq {c L d s : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) :
    (c / (2 * L)) * d / (2 * c) * s = d / (4 * L) * s := by
  field_simp; ring

end Entropic.Extensions20261115.DirectionRecord
