import Mathlib

/-! The qutrit-qubit link as the electroweak record: algebra behind Appendix S.10.

A link between a qutrit and a qubit has identification algebra su(3) + su(2) + u(1) acting on
`C^2 ⊗ C^3`. Its centre `Q = diag(3·1_2, -2·1_3)` is traceless on `C^2 ⊕ C^3` and acts on the link
as the scalar `3 - 2 = 1`, so `Y = Q/6` gives the link hypercharge `1/6`. A cube root of unity
`ω·1_3` has determinant one, so it lies in `S(U(3) × U(2))`. It acts on the link as `ω` and trivially
on every conjugation channel, so the link carries the triality that the projective `PU(3)` channel of
Appendix I.2 cannot see.

For the stiffness, the isotropic qutrit channel `t X + c Tr(X) I` compressed onto any two-dimensional
support multiplies every traceless operator by `t`. Carried through the color channel, a qubit
record therefore gets `13/14`. A record pinned to the unit-amplitude doublet gets `1`. The required
`SU(2)_L` multiplier `0.94915` lies strictly between these two limits.

The read cap is used only as a named hypothesis: positive maps between the ends are all decomposable
exactly when `d₁ d₂ ≤ 6` (Størmer 1963, Woronowicz 1976, Choi 1975). Physical identifications (which
records exist, the frame alignment, electric charge) are not formalized. -/

namespace Entropic.Electromagnetism.ReadableLink

open Matrix
open scoped Kronecker

/-! ## The central charge -/

/-- `Q = diag(d₂·1_{d₁}, -d₁·1_{d₂})` is traceless on `C^{d₁} ⊕ C^{d₂}`. -/
theorem center_traceless (d₁ d₂ : ℚ) : d₁ * d₂ + d₂ * (-d₁) = 0 := by ring

/-- On the link `C^{d₁} ⊗ C^{d₂}`, `ξ₁ ⊗ 1 + 1 ⊗ ξ₂` with `ξ₁ = d₂·1`, `ξ₂ = -d₁·1` is the scalar
`d₂ - d₁`. -/
theorem center_acts_as_scalar {R : Type*} [CommRing R] (m n : Type*) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (d₁ d₂ : R) :
    ((d₂ • (1 : Matrix m m R)) ⊗ₖ (1 : Matrix n n R)) +
      ((1 : Matrix m m R) ⊗ₖ ((-d₁) • (1 : Matrix n n R))) =
      (d₂ - d₁) • (1 : Matrix (m × n) (m × n) R) := by
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, ← add_smul]
  congr 1
  ring

/-- The qubit-qutrit link: the centre acts as `3 - 2 = 1`. -/
theorem qubit_qutrit_charge {R : Type*} [CommRing R] :
    (((3:R) • (1 : Matrix (Fin 2) (Fin 2) R)) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) R)) +
      ((1 : Matrix (Fin 2) (Fin 2) R) ⊗ₖ ((-2:R) • (1 : Matrix (Fin 3) (Fin 3) R))) =
      (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) R) := by
  rw [center_acts_as_scalar]
  norm_num

/-- An equal-dimension link carries no central charge. -/
theorem equal_link_uncharged (d : ℚ) : d - d = 0 := by ring

/-- With `Y = Q/6`, the link hypercharge is `1/6` and `Y` on the five-dimensional sum is
`diag(1/2, 1/2, -1/3, -1/3, -1/3)`. -/
theorem link_hypercharge :
    ((3:ℚ) - 2) / 6 = 1/6 ∧ (3:ℚ)/6 = 1/2 ∧ (-2:ℚ)/6 = -1/3 := by norm_num

/-- The centre commutes with every block: a scalar block commutes with any operator on its
factor. -/
theorem scalar_block_commutes {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (c : R) (A : Matrix n n R) : (c • (1 : Matrix n n R)) * A = A * (c • 1) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-! ## Triality -/

/-- A cube root of unity on the qutrit has determinant one, so `(1_2, ω·1_3)` lies in
`S(U(2) × U(3))`. -/
theorem triality_det_one {R : Type*} [CommRing R] (ω : R) (h : ω ^ 3 = 1) :
    (ω • (1 : Matrix (Fin 3) (Fin 3) R)).det = 1 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, h, mul_one]

/-- On the link it acts as the scalar `ω`. -/
theorem triality_on_link {R : Type*} [CommRing R] (ω : R) :
    (1 : Matrix (Fin 2) (Fin 2) R) ⊗ₖ (ω • (1 : Matrix (Fin 3) (Fin 3) R)) =
      ω • (1 : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) R) := by
  rw [Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- Every conjugation channel is blind to it: `(ω·1) X (ω⁻¹·1) = X`. -/
theorem triality_channel_blind {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (ω ω' : R) (h : ω * ω' = 1) (X : Matrix n n R) :
    (ω • (1 : Matrix n n R)) * X * (ω' • 1) = X := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, h, one_smul]

/-! ## Stiffness of a qubit record -/

/-- The isotropic qutrit channel `Y ↦ t Y + c Tr(Y) I`, compressed onto a two-dimensional support
(`W V = 1`), multiplies every traceless operator by `t`. -/
theorem compressed_isotropic_channel {R : Type*} [CommRing R] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (t c : R) (V : Matrix n m R) (W : Matrix m n R) (hWV : W * V = 1)
    (X : Matrix m m R) (hX : X.trace = 0) :
    W * (t • (V * X * W) + (c * (V * X * W).trace) • (1 : Matrix n n R)) * V = t • X := by
  have htr : (V * X * W).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWV, Matrix.one_mul]
  rw [htr, hX, mul_zero, zero_smul, add_zero, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc W * (V * X * W) * V = (W * V) * X * (W * V) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hWV, Matrix.one_mul, Matrix.mul_one]

/-- Pinned limit: unit direct amplitude gives multiplier one, for any record dimension. -/
theorem pinned_limit (d : ℝ) : 1 - 2 * (1 - (1:ℝ)) / (d + 1) = 1 := by ring

/-- Isotropic limit: carried through the color channel, the qubit record gets `13/14`. -/
theorem isotropic_limit : (1:ℝ) - 2 * (1 - 6/7) / (3 + 1) = 13/14 := by norm_num

/-- The required `SU(2)_L` multiplier `0.94915` (Appendix S.10) lies strictly between the
isotropic and pinned limits. -/
theorem required_between_limits : (13:ℝ)/14 < 0.94915 ∧ (0.94915:ℝ) < 1 := by norm_num

/-! ## The read cap, as a named hypothesis -/

/-- No product of two integers at least two equals seven, so the cap `d₁ d₂ ≤ 6` separates
`(2,2)`, `(2,3)` from every type with `d₁ d₂ ≥ 8`. -/
theorem no_product_seven (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : a * b ≠ 7 := by
  intro h
  have : a ≤ 7 := by nlinarith
  interval_cases a <;> omega

/-- The readable types with unequal ends: only `(2,3)` and `(3,2)`. -/
theorem readable_unequal (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hcap : a * b ≤ 6) (hne : a ≠ b) :
    (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by
  have h1 : a ≤ 3 := by nlinarith
  have h2 : b ≤ 3 := by nlinarith
  interval_cases a <;> interval_cases b <;> simp_all

/-- Given the cited cap as a hypothesis, every link with an end of dimension at least four is
unreadable. The primitive slot (4), face alphabet (7), marked record (9) and shared face (16) are
all such ends. -/
theorem capacity_ends_unreadable (readable : ℕ → ℕ → Prop)
    (cap : ∀ a b, 2 ≤ a → 2 ≤ b → (readable a b ↔ a * b ≤ 6))
    (a b : ℕ) (ha : 2 ≤ a) (hb : 4 ≤ b) : ¬ readable a b := by
  rw [cap a b ha (by omega)]
  intro h
  nlinarith

/-! ## A fixed coupling beside an evolving `a₀` -/

/-- The diamond transfer multiplier depends only on the record's direct amplitude and dimension.
At any two Hubble rates the gauge multiplier is the same, while `a₀ = ε c H` changes by `H'/H`. -/
theorem coupling_fixed_a0_scales (ε c H H' k d : ℝ) (hε : ε ≠ 0) (hc : c ≠ 0) (hH : H ≠ 0) :
    (fun (_ : ℝ) => 1 - 2 * (1 - k) / (d + 1)) H = (fun (_ : ℝ) => 1 - 2 * (1 - k) / (d + 1)) H' ∧
      ε * c * H' / (ε * c * H) = H' / H := by
  refine ⟨rfl, ?_⟩
  field_simp

/-- At `z = 1.15`, the redshift of the ESPRESSO limit, `H(z)/H₀ > 1.95` for `Ω_m = 0.315`. -/
theorem a0_ratio_at_espresso_redshift :
    (1.95:ℝ) < Real.sqrt (0.315 * (1 + 1.15) ^ 3 + 0.685) := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

end Entropic.Electromagnetism.ReadableLink
