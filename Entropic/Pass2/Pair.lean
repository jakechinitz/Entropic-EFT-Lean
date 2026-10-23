import Mathlib.Tactic
import Entropic.Sweep.Spin

/-! Second pass, chunk 15: C04-37. On V_{3/2} ⊗ V_{3/2} (ladder basis) every matrix commuting with the
total J_z and J₊ is a combination of the four isotypic projectors P₃, P₂, P₁, P₀ = L_λ/d_λ of
`Sweep.SpinPair`. Proof: an explicit integer change of basis 𝒯 (columns J₋ᵏ v_J of the highest-weight
vectors) carries J_z, J₊ to block ladder form ⊕_J (H_J, P_J); the commutant there is spanned by the four
block identities E_J, and 𝒯 E_J 𝒯⁻¹ = P_J (kernel-checked integer identities). Hence a covariant Hessian
H(p) = A p² + B is ⊕_J (Z_J p² + r_J) I_{V_J}. -/

namespace Entropic.Pass2.Pair
open Matrix Entropic.Sweep.SpinPair

noncomputable section

def mulL {m k n : ℕ} (A : Fin m → Fin k → ℤ) (B : Fin k → Fin n → ℤ) : Fin m → Fin n → ℤ :=
  fun i j => (List.ofFn fun l => A i l * B l j).sum

theorem of_mul {m k n : ℕ} (A : Fin m → Fin k → ℤ) (B : Fin k → Fin n → ℤ) :
    Matrix.of A * Matrix.of B = Matrix.of (mulL A B) := by
  ext i j; simp [Matrix.mul_apply, mulL, List.sum_ofFn]

abbrev cast {m n : ℕ} (A : Fin m → Fin n → ℤ) : Matrix (Fin m) (Fin n) ℂ := (Matrix.of A).map (Int.castRingHom ℂ)

theorem cast_mul {m k n : ℕ} (A : Fin m → Fin k → ℤ) (B : Fin k → Fin n → ℤ) :
    cast A * cast B = cast (mulL A B) := by
  rw [cast, cast, ← Matrix.map_mul, of_mul]

theorem cast_ext {m n : ℕ} (A B : Fin m → Fin n → ℤ) (h : ∀ i j, A i j = B i j) : cast A = cast B := by
  ext i j; simp [h i j]

/-- Total J_z (doubled weights) and J₊ on V_{3/2} ⊗ V_{3/2}, product ladder basis. -/
def HtF : Fin 16 → Fin 16 → ℤ := ![![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6]]
def PtF : Fin 16 → Fin 16 → ℤ := ![![0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def Ht : Matrix (Fin 16) (Fin 16) ℂ := cast HtF
def Pt : Matrix (Fin 16) (Fin 16) ℂ := cast PtF

/-- Coupled-basis change 𝒯 and D·𝒯⁻¹. -/
def TF : Fin 16 → Fin 16 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 12, 0, 0, 0, 0, 0, -4, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 36, 0, 0, 0, 0, 0, -12, 0, 0, 0, 3, 0, -1],
    ![0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
    ![0, 0, 0, 108, 0, 0, 0, 0, 0, -12, 0, 0, 0, -1, 0, 1],
    ![0, 0, 0, 0, 432, 0, 0, 0, 0, 0, -72, 0, 0, 0, 6, 0],
    ![0, 0, 12, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 108, 0, 0, 0, 0, 0, 12, 0, 0, 0, -1, 0, -1],
    ![0, 0, 0, 0, 864, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0],
    ![0, 0, 0, 0, 0, 4320, 0, 0, 0, 0, 0, -288, 0, 0, 0, 0],
    ![0, 0, 0, 36, 0, 0, 0, 0, 0, 12, 0, 0, 0, 3, 0, 1],
    ![0, 0, 0, 0, 432, 0, 0, 0, 0, 0, 72, 0, 0, 0, 6, 0],
    ![0, 0, 0, 0, 0, 4320, 0, 0, 0, 0, 0, 288, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 25920, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def SF : Fin 16 → Fin 16 → ℤ := ![![25920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4320, 0, 0, 4320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 432, 0, 0, 864, 0, 0, 432, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 36, 0, 0, 108, 0, 0, 108, 0, 0, 36, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 18, 0, 0, 12, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, -12960, 0, 0, 12960, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -3240, 0, 0, 0, 0, 0, 3240, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -540, 0, 0, -540, 0, 0, 540, 0, 0, 540, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -180, 0, 0, 0, 0, 0, 180, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45, 0, 0, 45, 0],
    ![0, 0, 7776, 0, 0, -10368, 0, 0, 7776, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3888, 0, 0, -1296, 0, 0, -1296, 0, 0, 3888, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1296, 0, 0, -1296, 0, 0, 1296, 0, 0],
    ![0, 0, 0, -6480, 0, 0, 6480, 0, 0, -6480, 0, 0, 6480, 0, 0, 0]]
/-- Block ladder form: J_z and J₊ on V₃ ⊕ V₂ ⊕ V₁ ⊕ V₀. -/
def HcF : Fin 16 → Fin 16 → ℤ := ![![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def PcF : Fin 16 → Fin 16 → ℤ := ![![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def E3F : Fin 16 → Fin 16 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def E2F : Fin 16 → Fin 16 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def E1F : Fin 16 → Fin 16 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def E0F : Fin 16 → Fin 16 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

def P3c : Matrix (Fin 16) (Fin 16) ℂ := (1/5760 : ℂ) • cast L0F
def P2c : Matrix (Fin 16) (Fin 16) ℂ := (1/1152 : ℂ) • cast L12F
def P1c : Matrix (Fin 16) (Fin 16) ℂ := (1/640 : ℂ) • cast L20F
def P0c : Matrix (Fin 16) (Fin 16) ℂ := (1/1152 : ℂ) • cast L24F

set_option maxRecDepth 100000 in
theorem int_checks :
    (∀ i j, mulL HtF TF i j = mulL TF HcF i j) ∧ (∀ i j, mulL PtF TF i j = mulL TF PcF i j) ∧
    (∀ i j, mulL TF SF i j = if i = j then 25920 else 0) ∧ (∀ i j, mulL SF TF i j = if i = j then 25920 else 0) ∧
    (∀ i j, 5760 * mulL (mulL TF E3F) SF i j = 25920 * L0F i j) ∧
    (∀ i j, 1152 * mulL (mulL TF E2F) SF i j = 25920 * L12F i j) ∧
    (∀ i j, 640 * mulL (mulL TF E1F) SF i j = 25920 * L20F i j) ∧
    (∀ i j, 1152 * mulL (mulL TF E0F) SF i j = 25920 * L24F i j) := by
  decide +kernel

def Tc : Matrix (Fin 16) (Fin 16) ℂ := cast TF
def Sc : Matrix (Fin 16) (Fin 16) ℂ := (1/25920 : ℂ) • cast SF
def Hcc : Matrix (Fin 16) (Fin 16) ℂ := cast HcF
def Pcc : Matrix (Fin 16) (Fin 16) ℂ := cast PcF

theorem scalar_cast (k : ℤ) (A : Fin 16 → Fin 16 → ℤ) (h : ∀ i j, A i j = if i = j then k else 0) :
    cast A = (k : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
  ext i j; by_cases hij : i = j
  · subst hij; simp [h i i]
  · simp [h i j, Matrix.one_apply, hij]

theorem ST : Sc * Tc = 1 ∧ Tc * Sc = 1 := by
  obtain ⟨-, -, c3, c4, -⟩ := int_checks
  constructor
  · rw [Sc, Tc, Matrix.smul_mul, cast_mul, scalar_cast _ _ c4, smul_smul]; norm_num
  · rw [Sc, Tc, Matrix.mul_smul, cast_mul, scalar_cast _ _ c3, smul_smul]; norm_num

theorem intertwine : Ht * Tc = Tc * Hcc ∧ Pt * Tc = Tc * Pcc := by
  obtain ⟨c1, c2, -⟩ := int_checks
  exact ⟨by rw [Ht, Tc, Hcc, cast_mul, cast_mul, cast_ext _ _ c1],
    by rw [Pt, Tc, Pcc, cast_mul, cast_mul, cast_ext _ _ c2]⟩

theorem proj_eq (EF LF : Fin 16 → Fin 16 → ℤ) (dJ : ℕ) (hd : (dJ : ℂ) ≠ 0)
    (h : ∀ i j, (dJ : ℤ) * mulL (mulL TF EF) SF i j = 25920 * LF i j) :
    Tc * cast EF * Sc = (1 / dJ : ℂ) • cast LF := by
  rw [Sc, Tc, Matrix.mul_smul, cast_mul, cast_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, eq_intCast, smul_eq_mul]
  have e : ((dJ : ℤ) : ℂ) * (mulL (mulL TF EF) SF i j : ℂ) = ((25920 : ℤ) : ℂ) * (LF i j : ℂ) := by
    exact_mod_cast h i j
  push_cast at e
  field_simp
  linear_combination e

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The commutant of the block ladder form ⊕_J (H_J, P_J) is spanned by the block identities. -/
theorem coupled_commutant (Y : Matrix (Fin 16) (Fin 16) ℂ) (h1 : Y * Hcc = Hcc * Y) (h2 : Y * Pcc = Pcc * Y) :
    Y = Y 0 0 • cast E3F + Y 7 7 • cast E2F + Y 12 12 • cast E1F + Y 15 15 • cast E0F := by
  have f_0_1 : Y 0 1 = 0 := by
    have q0 := congrFun (congrFun h1 0) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_0_2 : Y 0 2 = 0 := by
    have q0 := congrFun (congrFun h1 0) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_0_3 : Y 0 3 = 0 := by
    have q0 := congrFun (congrFun h1 0) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_0_4 : Y 0 4 = 0 := by
    have q0 := congrFun (congrFun h1 0) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_0_5 : Y 0 5 = 0 := by
    have q0 := congrFun (congrFun h1 0) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0
  have f_0_6 : Y 0 6 = 0 := by
    have q0 := congrFun (congrFun h1 0) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_0_7 : Y 0 7 = 0 := by
    have q0 := congrFun (congrFun h1 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_0_8 : Y 0 8 = 0 := by
    have q0 := congrFun (congrFun h1 0) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_0_9 : Y 0 9 = 0 := by
    have q0 := congrFun (congrFun h1 0) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_0_10 : Y 0 10 = 0 := by
    have q0 := congrFun (congrFun h1 0) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_0_11 : Y 0 11 = 0 := by
    have q0 := congrFun (congrFun h1 0) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0
  have f_0_12 : Y 0 12 = 0 := by
    have q0 := congrFun (congrFun h1 0) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_0_13 : Y 0 13 = 0 := by
    have q0 := congrFun (congrFun h1 0) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_0_14 : Y 0 14 = 0 := by
    have q0 := congrFun (congrFun h1 0) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_0_15 : Y 0 15 = 0 := by
    have q0 := congrFun (congrFun h1 0) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_1_0 : Y 1 0 = 0 := by
    have q0 := congrFun (congrFun h1 1) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_1_1 : Y 1 1 = (1:ℂ) * Y 0 0 := by
    have q0 := congrFun (congrFun h2 0) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_1_2 : Y 1 2 = 0 := by
    have q0 := congrFun (congrFun h1 1) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_1_3 : Y 1 3 = 0 := by
    have q0 := congrFun (congrFun h1 1) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_1_4 : Y 1 4 = 0 := by
    have q0 := congrFun (congrFun h1 1) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_1_5 : Y 1 5 = 0 := by
    have q0 := congrFun (congrFun h1 1) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_1_6 : Y 1 6 = 0 := by
    have q0 := congrFun (congrFun h1 1) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0
  have f_1_7 : Y 1 7 = 0 := by
    have q0 := congrFun (congrFun h2 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_1_8 : Y 1 8 = 0 := by
    have q0 := congrFun (congrFun h1 1) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_1_9 : Y 1 9 = 0 := by
    have q0 := congrFun (congrFun h1 1) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_1_10 : Y 1 10 = 0 := by
    have q0 := congrFun (congrFun h1 1) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_1_11 : Y 1 11 = 0 := by
    have q0 := congrFun (congrFun h1 1) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_1_12 : Y 1 12 = 0 := by
    have q0 := congrFun (congrFun h1 1) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_1_13 : Y 1 13 = 0 := by
    have q0 := congrFun (congrFun h1 1) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_1_14 : Y 1 14 = 0 := by
    have q0 := congrFun (congrFun h1 1) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_1_15 : Y 1 15 = 0 := by
    have q0 := congrFun (congrFun h1 1) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_2_0 : Y 2 0 = 0 := by
    have q0 := congrFun (congrFun h1 2) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_2_1 : Y 2 1 = 0 := by
    have q0 := congrFun (congrFun h1 2) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_2_2 : Y 2 2 = (1:ℂ) * Y 0 0 := by
    have q0 := congrFun (congrFun h2 0) 1
    have q1 := congrFun (congrFun h2 1) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0 + ((-1:ℂ)/10) * q1
  have f_2_3 : Y 2 3 = 0 := by
    have q0 := congrFun (congrFun h1 2) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_2_4 : Y 2 4 = 0 := by
    have q0 := congrFun (congrFun h1 2) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_2_5 : Y 2 5 = 0 := by
    have q0 := congrFun (congrFun h1 2) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_2_6 : Y 2 6 = 0 := by
    have q0 := congrFun (congrFun h1 2) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_2_7 : Y 2 7 = 0 := by
    have q0 := congrFun (congrFun h1 2) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_2_8 : Y 2 8 = 0 := by
    have q0 := congrFun (congrFun h2 1) 8
    have q1 := congrFun (congrFun h2 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0 + ((-1:ℂ)/15) * q1
  have f_2_9 : Y 2 9 = 0 := by
    have q0 := congrFun (congrFun h1 2) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_2_10 : Y 2 10 = 0 := by
    have q0 := congrFun (congrFun h1 2) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_2_11 : Y 2 11 = 0 := by
    have q0 := congrFun (congrFun h1 2) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_2_12 : Y 2 12 = 0 := by
    have q0 := congrFun (congrFun h2 1) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0
  have f_2_13 : Y 2 13 = 0 := by
    have q0 := congrFun (congrFun h1 2) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_2_14 : Y 2 14 = 0 := by
    have q0 := congrFun (congrFun h1 2) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_2_15 : Y 2 15 = 0 := by
    have q0 := congrFun (congrFun h1 2) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_0 : Y 3 0 = 0 := by
    have q0 := congrFun (congrFun h1 3) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_3_1 : Y 3 1 = 0 := by
    have q0 := congrFun (congrFun h1 3) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_3_2 : Y 3 2 = 0 := by
    have q0 := congrFun (congrFun h1 3) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_3_3 : Y 3 3 = (1:ℂ) * Y 0 0 := by
    have q0 := congrFun (congrFun h2 0) 1
    have q1 := congrFun (congrFun h2 1) 2
    have q2 := congrFun (congrFun h2 2) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0 + ((-1:ℂ)/10) * q1 + ((-1:ℂ)/12) * q2
  have f_3_4 : Y 3 4 = 0 := by
    have q0 := congrFun (congrFun h1 3) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_5 : Y 3 5 = 0 := by
    have q0 := congrFun (congrFun h1 3) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_3_6 : Y 3 6 = 0 := by
    have q0 := congrFun (congrFun h1 3) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_3_7 : Y 3 7 = 0 := by
    have q0 := congrFun (congrFun h1 3) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_3_8 : Y 3 8 = 0 := by
    have q0 := congrFun (congrFun h1 3) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_3_9 : Y 3 9 = 0 := by
    have q0 := congrFun (congrFun h2 2) 9
    have q1 := congrFun (congrFun h2 1) 8
    have q2 := congrFun (congrFun h2 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/12) * q0 + ((-1:ℂ)/20) * q1 + ((-1:ℂ)/30) * q2
  have f_3_10 : Y 3 10 = 0 := by
    have q0 := congrFun (congrFun h1 3) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_11 : Y 3 11 = 0 := by
    have q0 := congrFun (congrFun h1 3) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_3_12 : Y 3 12 = 0 := by
    have q0 := congrFun (congrFun h1 3) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_3_13 : Y 3 13 = 0 := by
    have q0 := congrFun (congrFun h2 2) 13
    have q1 := congrFun (congrFun h2 1) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/12) * q0 + ((-1:ℂ)/60) * q1
  have f_3_14 : Y 3 14 = 0 := by
    have q0 := congrFun (congrFun h1 3) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_15 : Y 3 15 = 0 := by
    have q0 := congrFun (congrFun h2 2) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/12) * q0
  have f_4_0 : Y 4 0 = 0 := by
    have q0 := congrFun (congrFun h1 4) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_4_1 : Y 4 1 = 0 := by
    have q0 := congrFun (congrFun h1 4) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_4_2 : Y 4 2 = 0 := by
    have q0 := congrFun (congrFun h1 4) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_4_3 : Y 4 3 = 0 := by
    have q0 := congrFun (congrFun h1 4) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_4_4 : Y 4 4 = (1:ℂ) * Y 0 0 := by
    have q0 := congrFun (congrFun h2 0) 1
    have q1 := congrFun (congrFun h2 1) 2
    have q2 := congrFun (congrFun h2 2) 3
    have q3 := congrFun (congrFun h2 3) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0 + ((-1:ℂ)/10) * q1 + ((-1:ℂ)/12) * q2 + ((-1:ℂ)/12) * q3
  have f_4_5 : Y 4 5 = 0 := by
    have q0 := congrFun (congrFun h1 4) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_4_6 : Y 4 6 = 0 := by
    have q0 := congrFun (congrFun h1 4) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_4_7 : Y 4 7 = 0 := by
    have q0 := congrFun (congrFun h1 4) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_4_8 : Y 4 8 = 0 := by
    have q0 := congrFun (congrFun h1 4) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_4_9 : Y 4 9 = 0 := by
    have q0 := congrFun (congrFun h1 4) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_4_10 : Y 4 10 = 0 := by
    have q0 := congrFun (congrFun h2 3) 10
    have q1 := congrFun (congrFun h2 2) 9
    have q2 := congrFun (congrFun h2 1) 8
    have q3 := congrFun (congrFun h2 0) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/12) * q0 + ((-1:ℂ)/24) * q1 + ((-1:ℂ)/40) * q2 + ((-1:ℂ)/60) * q3
  have f_4_11 : Y 4 11 = 0 := by
    have q0 := congrFun (congrFun h1 4) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_4_12 : Y 4 12 = 0 := by
    have q0 := congrFun (congrFun h1 4) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_4_13 : Y 4 13 = 0 := by
    have q0 := congrFun (congrFun h1 4) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_4_14 : Y 4 14 = 0 := by
    have q0 := congrFun (congrFun h2 3) 14
    have q1 := congrFun (congrFun h2 2) 13
    have q2 := congrFun (congrFun h2 1) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/12) * q0 + ((-1:ℂ)/72) * q1 + ((-1:ℂ)/360) * q2
  have f_4_15 : Y 4 15 = 0 := by
    have q0 := congrFun (congrFun h1 4) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_0 : Y 5 0 = 0 := by
    have q0 := congrFun (congrFun h1 5) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0
  have f_5_1 : Y 5 1 = 0 := by
    have q0 := congrFun (congrFun h1 5) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_5_2 : Y 5 2 = 0 := by
    have q0 := congrFun (congrFun h1 5) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_5_3 : Y 5 3 = 0 := by
    have q0 := congrFun (congrFun h1 5) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_5_4 : Y 5 4 = 0 := by
    have q0 := congrFun (congrFun h1 5) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_6 : Y 5 6 = 0 := by
    have q0 := congrFun (congrFun h1 5) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_5_7 : Y 5 7 = 0 := by
    have q0 := congrFun (congrFun h1 5) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_5_8 : Y 5 8 = 0 := by
    have q0 := congrFun (congrFun h1 5) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_5_9 : Y 5 9 = 0 := by
    have q0 := congrFun (congrFun h1 5) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_5_10 : Y 5 10 = 0 := by
    have q0 := congrFun (congrFun h1 5) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_12 : Y 5 12 = 0 := by
    have q0 := congrFun (congrFun h1 5) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_5_13 : Y 5 13 = 0 := by
    have q0 := congrFun (congrFun h1 5) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_5_14 : Y 5 14 = 0 := by
    have q0 := congrFun (congrFun h1 5) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_15 : Y 5 15 = 0 := by
    have q0 := congrFun (congrFun h1 5) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_6_0 : Y 6 0 = 0 := by
    have q0 := congrFun (congrFun h1 6) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_6_1 : Y 6 1 = 0 := by
    have q0 := congrFun (congrFun h1 6) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0
  have f_6_2 : Y 6 2 = 0 := by
    have q0 := congrFun (congrFun h1 6) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_6_3 : Y 6 3 = 0 := by
    have q0 := congrFun (congrFun h1 6) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_6_4 : Y 6 4 = 0 := by
    have q0 := congrFun (congrFun h1 6) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_6_5 : Y 6 5 = 0 := by
    have q0 := congrFun (congrFun h1 6) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_6_7 : Y 6 7 = 0 := by
    have q0 := congrFun (congrFun h1 6) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0
  have f_6_8 : Y 6 8 = 0 := by
    have q0 := congrFun (congrFun h1 6) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_6_9 : Y 6 9 = 0 := by
    have q0 := congrFun (congrFun h1 6) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_6_10 : Y 6 10 = 0 := by
    have q0 := congrFun (congrFun h1 6) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_6_11 : Y 6 11 = 0 := by
    have q0 := congrFun (congrFun h1 6) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_6_12 : Y 6 12 = 0 := by
    have q0 := congrFun (congrFun h1 6) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_6_13 : Y 6 13 = 0 := by
    have q0 := congrFun (congrFun h1 6) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_6_14 : Y 6 14 = 0 := by
    have q0 := congrFun (congrFun h1 6) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_6_15 : Y 6 15 = 0 := by
    have q0 := congrFun (congrFun h1 6) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_7_0 : Y 7 0 = 0 := by
    have q0 := congrFun (congrFun h1 7) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_7_2 : Y 7 2 = 0 := by
    have q0 := congrFun (congrFun h1 7) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_7_3 : Y 7 3 = 0 := by
    have q0 := congrFun (congrFun h1 7) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_7_4 : Y 7 4 = 0 := by
    have q0 := congrFun (congrFun h1 7) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_7_5 : Y 7 5 = 0 := by
    have q0 := congrFun (congrFun h1 7) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_7_6 : Y 7 6 = 0 := by
    have q0 := congrFun (congrFun h1 7) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0
  have f_7_8 : Y 7 8 = 0 := by
    have q0 := congrFun (congrFun h1 7) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_7_9 : Y 7 9 = 0 := by
    have q0 := congrFun (congrFun h1 7) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_7_10 : Y 7 10 = 0 := by
    have q0 := congrFun (congrFun h1 7) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_7_11 : Y 7 11 = 0 := by
    have q0 := congrFun (congrFun h1 7) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_7_12 : Y 7 12 = 0 := by
    have q0 := congrFun (congrFun h1 7) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_7_13 : Y 7 13 = 0 := by
    have q0 := congrFun (congrFun h1 7) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_7_14 : Y 7 14 = 0 := by
    have q0 := congrFun (congrFun h1 7) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_7_15 : Y 7 15 = 0 := by
    have q0 := congrFun (congrFun h1 7) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_8_0 : Y 8 0 = 0 := by
    have q0 := congrFun (congrFun h1 8) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_8_1 : Y 8 1 = 0 := by
    have q0 := congrFun (congrFun h1 8) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_8_2 : Y 8 2 = 0 := by
    have q0 := congrFun (congrFun h2 8) 3
    have q1 := congrFun (congrFun h2 9) 4
    have q2 := congrFun (congrFun h2 10) 5
    have q3 := congrFun (congrFun h2 11) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/12) * q0 + ((1:ℂ)/24) * q1 + ((1:ℂ)/40) * q2 + ((1:ℂ)/60) * q3
  have f_8_3 : Y 8 3 = 0 := by
    have q0 := congrFun (congrFun h1 8) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_8_4 : Y 8 4 = 0 := by
    have q0 := congrFun (congrFun h1 8) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_8_5 : Y 8 5 = 0 := by
    have q0 := congrFun (congrFun h1 8) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_8_6 : Y 8 6 = 0 := by
    have q0 := congrFun (congrFun h1 8) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_8_7 : Y 8 7 = 0 := by
    have q0 := congrFun (congrFun h1 8) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_8_8 : Y 8 8 = (1:ℂ) * Y 7 7 := by
    have q0 := congrFun (congrFun h2 7) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_8_9 : Y 8 9 = 0 := by
    have q0 := congrFun (congrFun h1 8) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_8_10 : Y 8 10 = 0 := by
    have q0 := congrFun (congrFun h1 8) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_8_11 : Y 8 11 = 0 := by
    have q0 := congrFun (congrFun h1 8) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_8_12 : Y 8 12 = 0 := by
    have q0 := congrFun (congrFun h2 7) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_8_13 : Y 8 13 = 0 := by
    have q0 := congrFun (congrFun h1 8) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_8_14 : Y 8 14 = 0 := by
    have q0 := congrFun (congrFun h1 8) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_8_15 : Y 8 15 = 0 := by
    have q0 := congrFun (congrFun h1 8) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_9_0 : Y 9 0 = 0 := by
    have q0 := congrFun (congrFun h1 9) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_9_1 : Y 9 1 = 0 := by
    have q0 := congrFun (congrFun h1 9) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_9_2 : Y 9 2 = 0 := by
    have q0 := congrFun (congrFun h1 9) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_9_3 : Y 9 3 = 0 := by
    have q0 := congrFun (congrFun h2 9) 4
    have q1 := congrFun (congrFun h2 10) 5
    have q2 := congrFun (congrFun h2 11) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/12) * q0 + ((1:ℂ)/20) * q1 + ((1:ℂ)/30) * q2
  have f_9_4 : Y 9 4 = 0 := by
    have q0 := congrFun (congrFun h1 9) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_9_5 : Y 9 5 = 0 := by
    have q0 := congrFun (congrFun h1 9) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_9_6 : Y 9 6 = 0 := by
    have q0 := congrFun (congrFun h1 9) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_9_7 : Y 9 7 = 0 := by
    have q0 := congrFun (congrFun h1 9) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_9_8 : Y 9 8 = 0 := by
    have q0 := congrFun (congrFun h1 9) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_9_9 : Y 9 9 = (1:ℂ) * Y 7 7 := by
    have q0 := congrFun (congrFun h2 7) 8
    have q1 := congrFun (congrFun h2 8) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0 + ((-1:ℂ)/6) * q1
  have f_9_10 : Y 9 10 = 0 := by
    have q0 := congrFun (congrFun h1 9) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_9_11 : Y 9 11 = 0 := by
    have q0 := congrFun (congrFun h1 9) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_9_12 : Y 9 12 = 0 := by
    have q0 := congrFun (congrFun h1 9) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_9_13 : Y 9 13 = 0 := by
    have q0 := congrFun (congrFun h2 8) 13
    have q1 := congrFun (congrFun h2 7) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0 + ((-1:ℂ)/12) * q1
  have f_9_14 : Y 9 14 = 0 := by
    have q0 := congrFun (congrFun h1 9) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_9_15 : Y 9 15 = 0 := by
    have q0 := congrFun (congrFun h2 8) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_10_0 : Y 10 0 = 0 := by
    have q0 := congrFun (congrFun h1 10) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_10_1 : Y 10 1 = 0 := by
    have q0 := congrFun (congrFun h1 10) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_10_2 : Y 10 2 = 0 := by
    have q0 := congrFun (congrFun h1 10) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_10_3 : Y 10 3 = 0 := by
    have q0 := congrFun (congrFun h1 10) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_10_4 : Y 10 4 = 0 := by
    have q0 := congrFun (congrFun h2 10) 5
    have q1 := congrFun (congrFun h2 11) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0 + ((1:ℂ)/15) * q1
  have f_10_5 : Y 10 5 = 0 := by
    have q0 := congrFun (congrFun h1 10) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_10_6 : Y 10 6 = 0 := by
    have q0 := congrFun (congrFun h1 10) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_10_7 : Y 10 7 = 0 := by
    have q0 := congrFun (congrFun h1 10) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_10_8 : Y 10 8 = 0 := by
    have q0 := congrFun (congrFun h1 10) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_10_9 : Y 10 9 = 0 := by
    have q0 := congrFun (congrFun h1 10) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_10_10 : Y 10 10 = (1:ℂ) * Y 7 7 := by
    have q0 := congrFun (congrFun h2 7) 8
    have q1 := congrFun (congrFun h2 8) 9
    have q2 := congrFun (congrFun h2 9) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0 + ((-1:ℂ)/6) * q1 + ((-1:ℂ)/6) * q2
  have f_10_11 : Y 10 11 = 0 := by
    have q0 := congrFun (congrFun h1 10) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_10_12 : Y 10 12 = 0 := by
    have q0 := congrFun (congrFun h1 10) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_10_13 : Y 10 13 = 0 := by
    have q0 := congrFun (congrFun h1 10) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_10_14 : Y 10 14 = 0 := by
    have q0 := congrFun (congrFun h2 9) 14
    have q1 := congrFun (congrFun h2 8) 13
    have q2 := congrFun (congrFun h2 7) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0 + ((-1:ℂ)/18) * q1 + ((-1:ℂ)/36) * q2
  have f_10_15 : Y 10 15 = 0 := by
    have q0 := congrFun (congrFun h1 10) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_11_0 : Y 11 0 = 0 := by
    have q0 := congrFun (congrFun h1 11) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0
  have f_11_1 : Y 11 1 = 0 := by
    have q0 := congrFun (congrFun h1 11) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_11_2 : Y 11 2 = 0 := by
    have q0 := congrFun (congrFun h1 11) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_11_3 : Y 11 3 = 0 := by
    have q0 := congrFun (congrFun h1 11) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_11_4 : Y 11 4 = 0 := by
    have q0 := congrFun (congrFun h1 11) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_11_5 : Y 11 5 = 0 := by
    have q0 := congrFun (congrFun h2 11) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_11_6 : Y 11 6 = 0 := by
    have q0 := congrFun (congrFun h1 11) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_11_7 : Y 11 7 = 0 := by
    have q0 := congrFun (congrFun h1 11) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_11_8 : Y 11 8 = 0 := by
    have q0 := congrFun (congrFun h1 11) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_11_9 : Y 11 9 = 0 := by
    have q0 := congrFun (congrFun h1 11) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_11_10 : Y 11 10 = 0 := by
    have q0 := congrFun (congrFun h1 11) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_11_11 : Y 11 11 = (1:ℂ) * Y 7 7 := by
    have q0 := congrFun (congrFun h2 7) 8
    have q1 := congrFun (congrFun h2 8) 9
    have q2 := congrFun (congrFun h2 9) 10
    have q3 := congrFun (congrFun h2 10) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0 + ((-1:ℂ)/6) * q1 + ((-1:ℂ)/6) * q2 + ((-1:ℂ)/4) * q3
  have f_11_12 : Y 11 12 = 0 := by
    have q0 := congrFun (congrFun h1 11) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_11_13 : Y 11 13 = 0 := by
    have q0 := congrFun (congrFun h1 11) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_11_14 : Y 11 14 = 0 := by
    have q0 := congrFun (congrFun h1 11) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_11_15 : Y 11 15 = 0 := by
    have q0 := congrFun (congrFun h1 11) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_12_0 : Y 12 0 = 0 := by
    have q0 := congrFun (congrFun h1 12) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_12_1 : Y 12 1 = 0 := by
    have q0 := congrFun (congrFun h1 12) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_12_2 : Y 12 2 = 0 := by
    have q0 := congrFun (congrFun h2 12) 3
    have q1 := congrFun (congrFun h2 13) 4
    have q2 := congrFun (congrFun h2 14) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/12) * q0 + ((1:ℂ)/72) * q1 + ((1:ℂ)/360) * q2
  have f_12_3 : Y 12 3 = 0 := by
    have q0 := congrFun (congrFun h1 12) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_12_4 : Y 12 4 = 0 := by
    have q0 := congrFun (congrFun h1 12) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_12_5 : Y 12 5 = 0 := by
    have q0 := congrFun (congrFun h1 12) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_12_6 : Y 12 6 = 0 := by
    have q0 := congrFun (congrFun h1 12) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_12_7 : Y 12 7 = 0 := by
    have q0 := congrFun (congrFun h1 12) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_12_8 : Y 12 8 = 0 := by
    have q0 := congrFun (congrFun h2 12) 9
    have q1 := congrFun (congrFun h2 13) 10
    have q2 := congrFun (congrFun h2 14) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0 + ((1:ℂ)/18) * q1 + ((1:ℂ)/36) * q2
  have f_12_9 : Y 12 9 = 0 := by
    have q0 := congrFun (congrFun h1 12) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_12_10 : Y 12 10 = 0 := by
    have q0 := congrFun (congrFun h1 12) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_12_11 : Y 12 11 = 0 := by
    have q0 := congrFun (congrFun h1 12) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_12_13 : Y 12 13 = 0 := by
    have q0 := congrFun (congrFun h1 12) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_12_14 : Y 12 14 = 0 := by
    have q0 := congrFun (congrFun h1 12) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_12_15 : Y 12 15 = 0 := by
    have q0 := congrFun (congrFun h1 12) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_13_0 : Y 13 0 = 0 := by
    have q0 := congrFun (congrFun h1 13) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_13_1 : Y 13 1 = 0 := by
    have q0 := congrFun (congrFun h1 13) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_13_2 : Y 13 2 = 0 := by
    have q0 := congrFun (congrFun h1 13) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_13_3 : Y 13 3 = 0 := by
    have q0 := congrFun (congrFun h2 13) 4
    have q1 := congrFun (congrFun h2 14) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/12) * q0 + ((1:ℂ)/60) * q1
  have f_13_4 : Y 13 4 = 0 := by
    have q0 := congrFun (congrFun h1 13) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_13_5 : Y 13 5 = 0 := by
    have q0 := congrFun (congrFun h1 13) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_13_6 : Y 13 6 = 0 := by
    have q0 := congrFun (congrFun h1 13) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_13_7 : Y 13 7 = 0 := by
    have q0 := congrFun (congrFun h1 13) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_13_8 : Y 13 8 = 0 := by
    have q0 := congrFun (congrFun h1 13) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_13_9 : Y 13 9 = 0 := by
    have q0 := congrFun (congrFun h2 13) 10
    have q1 := congrFun (congrFun h2 14) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0 + ((1:ℂ)/12) * q1
  have f_13_10 : Y 13 10 = 0 := by
    have q0 := congrFun (congrFun h1 13) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_13_11 : Y 13 11 = 0 := by
    have q0 := congrFun (congrFun h1 13) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_13_12 : Y 13 12 = 0 := by
    have q0 := congrFun (congrFun h1 13) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_13_13 : Y 13 13 = (1:ℂ) * Y 12 12 := by
    have q0 := congrFun (congrFun h2 12) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_13_14 : Y 13 14 = 0 := by
    have q0 := congrFun (congrFun h1 13) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_13_15 : Y 13 15 = 0 := by
    have q0 := congrFun (congrFun h2 12) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_14_0 : Y 14 0 = 0 := by
    have q0 := congrFun (congrFun h1 14) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_14_1 : Y 14 1 = 0 := by
    have q0 := congrFun (congrFun h1 14) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_14_2 : Y 14 2 = 0 := by
    have q0 := congrFun (congrFun h1 14) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_14_3 : Y 14 3 = 0 := by
    have q0 := congrFun (congrFun h1 14) 3
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_14_4 : Y 14 4 = 0 := by
    have q0 := congrFun (congrFun h2 14) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0
  have f_14_5 : Y 14 5 = 0 := by
    have q0 := congrFun (congrFun h1 14) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_14_6 : Y 14 6 = 0 := by
    have q0 := congrFun (congrFun h1 14) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_14_7 : Y 14 7 = 0 := by
    have q0 := congrFun (congrFun h1 14) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_14_8 : Y 14 8 = 0 := by
    have q0 := congrFun (congrFun h1 14) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_14_9 : Y 14 9 = 0 := by
    have q0 := congrFun (congrFun h1 14) 9
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_14_10 : Y 14 10 = 0 := by
    have q0 := congrFun (congrFun h2 14) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_14_11 : Y 14 11 = 0 := by
    have q0 := congrFun (congrFun h1 14) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_14_12 : Y 14 12 = 0 := by
    have q0 := congrFun (congrFun h1 14) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_14_13 : Y 14 13 = 0 := by
    have q0 := congrFun (congrFun h1 14) 13
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_14_14 : Y 14 14 = (1:ℂ) * Y 12 12 := by
    have q0 := congrFun (congrFun h2 12) 13
    have q1 := congrFun (congrFun h2 13) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0 + ((-1:ℂ)/2) * q1
  have f_14_15 : Y 14 15 = 0 := by
    have q0 := congrFun (congrFun h1 14) 15
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_15_0 : Y 15 0 = 0 := by
    have q0 := congrFun (congrFun h1 15) 0
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_15_1 : Y 15 1 = 0 := by
    have q0 := congrFun (congrFun h1 15) 1
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_15_2 : Y 15 2 = 0 := by
    have q0 := congrFun (congrFun h1 15) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_15_3 : Y 15 3 = 0 := by
    have q0 := congrFun (congrFun h2 15) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/12) * q0
  have f_15_4 : Y 15 4 = 0 := by
    have q0 := congrFun (congrFun h1 15) 4
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_15_5 : Y 15 5 = 0 := by
    have q0 := congrFun (congrFun h1 15) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_15_6 : Y 15 6 = 0 := by
    have q0 := congrFun (congrFun h1 15) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_15_7 : Y 15 7 = 0 := by
    have q0 := congrFun (congrFun h1 15) 7
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_15_8 : Y 15 8 = 0 := by
    have q0 := congrFun (congrFun h1 15) 8
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_15_9 : Y 15 9 = 0 := by
    have q0 := congrFun (congrFun h2 15) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_15_10 : Y 15 10 = 0 := by
    have q0 := congrFun (congrFun h1 15) 10
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_15_11 : Y 15 11 = 0 := by
    have q0 := congrFun (congrFun h1 15) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_15_12 : Y 15 12 = 0 := by
    have q0 := congrFun (congrFun h1 15) 12
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_15_13 : Y 15 13 = 0 := by
    have q0 := congrFun (congrFun h2 15) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_15_14 : Y 15 14 = 0 := by
    have q0 := congrFun (congrFun h1 15) 14
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_5_5 : Y 5 5 = (1:ℂ) * Y 0 0 := by
    have q1 := congrFun (congrFun h2 4) 5
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) (1:ℂ) * f_4_4 + ((-1:ℂ)/10) * q1
  have f_5_11 : Y 5 11 = 0 := by
    have q0 := congrFun (congrFun h2 4) 11
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((-1:ℂ)/10) * q0 + ((2:ℂ)/5) * f_4_10
  have f_6_6 : Y 6 6 = (1:ℂ) * Y 0 0 := by
    have q1 := congrFun (congrFun h2 4) 5
    have q2 := congrFun (congrFun h2 5) 6
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) (1:ℂ) * f_4_4 + ((-1:ℂ)/10) * q1 + ((-1:ℂ)/6) * q2
  have f_7_1 : Y 7 1 = 0 := by
    have q0 := congrFun (congrFun h2 7) 2
    linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hcc, Pcc, cast, HcF, PcF, Matrix.map_apply, Matrix.of_apply] <;> ring_nf)) ((1:ℂ)/10) * q0 + ((2:ℂ)/5) * f_8_2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, E3F, E2F, E1F, E0F, f_0_1, f_0_2, f_0_3, f_0_4, f_0_5, f_0_6, f_0_7, f_0_8, f_0_9, f_0_10, f_0_11, f_0_12, f_0_13, f_0_14, f_0_15, f_1_0, f_1_1, f_1_2, f_1_3, f_1_4, f_1_5, f_1_6, f_1_7, f_1_8, f_1_9, f_1_10, f_1_11, f_1_12, f_1_13, f_1_14, f_1_15, f_2_0, f_2_1, f_2_2, f_2_3, f_2_4, f_2_5, f_2_6, f_2_7, f_2_8, f_2_9, f_2_10, f_2_11, f_2_12, f_2_13, f_2_14, f_2_15, f_3_0, f_3_1, f_3_2, f_3_3, f_3_4, f_3_5, f_3_6, f_3_7, f_3_8, f_3_9, f_3_10, f_3_11, f_3_12, f_3_13, f_3_14, f_3_15, f_4_0, f_4_1, f_4_2, f_4_3, f_4_4, f_4_5, f_4_6, f_4_7, f_4_8, f_4_9, f_4_10, f_4_11, f_4_12, f_4_13, f_4_14, f_4_15, f_5_0, f_5_1, f_5_2, f_5_3, f_5_4, f_5_6, f_5_7, f_5_8, f_5_9, f_5_10, f_5_12, f_5_13, f_5_14, f_5_15, f_6_0, f_6_1, f_6_2, f_6_3, f_6_4, f_6_5, f_6_7, f_6_8, f_6_9, f_6_10, f_6_11, f_6_12, f_6_13, f_6_14, f_6_15, f_7_0, f_7_2, f_7_3, f_7_4, f_7_5, f_7_6, f_7_8, f_7_9, f_7_10, f_7_11, f_7_12, f_7_13, f_7_14, f_7_15, f_8_0, f_8_1, f_8_2, f_8_3, f_8_4, f_8_5, f_8_6, f_8_7, f_8_8, f_8_9, f_8_10, f_8_11, f_8_12, f_8_13, f_8_14, f_8_15, f_9_0, f_9_1, f_9_2, f_9_3, f_9_4, f_9_5, f_9_6, f_9_7, f_9_8, f_9_9, f_9_10, f_9_11, f_9_12, f_9_13, f_9_14, f_9_15, f_10_0, f_10_1, f_10_2, f_10_3, f_10_4, f_10_5, f_10_6, f_10_7, f_10_8, f_10_9, f_10_10, f_10_11, f_10_12, f_10_13, f_10_14, f_10_15, f_11_0, f_11_1, f_11_2, f_11_3, f_11_4, f_11_5, f_11_6, f_11_7, f_11_8, f_11_9, f_11_10, f_11_11, f_11_12, f_11_13, f_11_14, f_11_15, f_12_0, f_12_1, f_12_2, f_12_3, f_12_4, f_12_5, f_12_6, f_12_7, f_12_8, f_12_9, f_12_10, f_12_11, f_12_13, f_12_14, f_12_15, f_13_0, f_13_1, f_13_2, f_13_3, f_13_4, f_13_5, f_13_6, f_13_7, f_13_8, f_13_9, f_13_10, f_13_11, f_13_12, f_13_13, f_13_14, f_13_15, f_14_0, f_14_1, f_14_2, f_14_3, f_14_4, f_14_5, f_14_6, f_14_7, f_14_8, f_14_9, f_14_10, f_14_11, f_14_12, f_14_13, f_14_14, f_14_15, f_15_0, f_15_1, f_15_2, f_15_3, f_15_4, f_15_5, f_15_6, f_15_7, f_15_8, f_15_9, f_15_10, f_15_11, f_15_12, f_15_13, f_15_14, f_5_5, f_5_11, f_6_6, f_7_1]

theorem conj_comm {A B : Matrix (Fin 16) (Fin 16) ℂ} (hAB : A * Tc = Tc * B) : Sc * A = B * Sc := by
  obtain ⟨st, ts⟩ := ST
  calc Sc * A = Sc * A * (Tc * Sc) := by rw [ts, Matrix.mul_one]
    _ = Sc * (A * Tc) * Sc := by simp only [Matrix.mul_assoc]
    _ = Sc * (Tc * B) * Sc := by rw [hAB]
    _ = B * Sc := by rw [← Matrix.mul_assoc Sc Tc B, st, Matrix.one_mul]

/-- C04-37 (j₀ = 3/2): X commuting with H_tot and J₊,tot is Σ_J c_J P_J. -/
theorem pair_commutant (X : Matrix (Fin 16) (Fin 16) ℂ) (h1 : X * Ht = Ht * X) (h2 : X * Pt = Pt * X) :
    ∃ c : Fin 4 → ℂ, X = c 0 • P3c + c 1 • P2c + c 2 • P1c + c 3 • P0c := by
  obtain ⟨st, ts⟩ := ST
  obtain ⟨i1, i2⟩ := intertwine
  obtain ⟨-, -, -, -, p3, p2, p1, p0⟩ := int_checks
  set Y := Sc * X * Tc with hY
  have comm : ∀ A B : Matrix (Fin 16) (Fin 16) ℂ, A * Tc = Tc * B → X * A = A * X → Y * B = B * Y := by
    intro A B hAB hXA
    calc Y * B = Sc * X * (Tc * B) := by rw [hY]; simp only [Matrix.mul_assoc]
      _ = Sc * (X * A) * Tc := by rw [← hAB]; simp only [Matrix.mul_assoc]
      _ = (Sc * A) * X * Tc := by rw [hXA]; simp only [Matrix.mul_assoc]
      _ = B * Y := by rw [conj_comm hAB, hY]; simp only [Matrix.mul_assoc]
  have hYc := coupled_commutant Y (comm _ _ i1 h1) (comm _ _ i2 h2)
  have hX : X = Tc * Y * Sc := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ts, Matrix.one_mul, Matrix.mul_assoc, ts, Matrix.mul_one]
  refine ⟨![Y 0 0, Y 7 7, Y 12 12, Y 15 15], ?_⟩
  rw [hX, hYc]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [proj_eq E3F L0F 5760 (by norm_num) (by exact_mod_cast p3),
    proj_eq E2F L12F 1152 (by norm_num) (by exact_mod_cast p2),
    proj_eq E1F L20F 640 (by norm_num) (by exact_mod_cast p1),
    proj_eq E0F L24F 1152 (by norm_num) (by exact_mod_cast p0)]
  simp [P3c, P2c, P1c, P0c, E3F, E2F, E1F, E0F]

/-- C04-37: if H(p) = A p² + B with A and B commuting with H_tot and J₊,tot, then
H(p) = Σ_J (Z_J p² + r_J) P_J with Z_J, r_J the block coefficients of A and B. -/
theorem covariant_hessian (A B : Matrix (Fin 16) (Fin 16) ℂ) (hA1 : A * Ht = Ht * A) (hA2 : A * Pt = Pt * A)
    (hB1 : B * Ht = Ht * B) (hB2 : B * Pt = Pt * B) :
    ∃ Z r : Fin 4 → ℂ, ∀ p : ℂ, p ^ 2 • A + B =
      (Z 0 * p ^ 2 + r 0) • P3c + (Z 1 * p ^ 2 + r 1) • P2c + (Z 2 * p ^ 2 + r 2) • P1c + (Z 3 * p ^ 2 + r 3) • P0c := by
  obtain ⟨a, ha⟩ := pair_commutant A hA1 hA2
  obtain ⟨b, hb⟩ := pair_commutant B hB1 hB2
  refine ⟨a, b, fun p => ?_⟩
  rw [ha, hb]
  module

end

end Entropic.Pass2.Pair
