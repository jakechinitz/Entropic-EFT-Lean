import Entropic.AppP.Spin

/-! Second pass, chunk 15: C07-51. An explicit SU(2)-equivariant map 𝓘 from H_mark = V₁ ⊗ V₁ onto the
complement Q = range P_Q ⊂ V_{3/2} ⊗ V_{3/2} (ladder bases), with left inverse 𝓛: 𝓛𝓘 = I₉, 𝓘𝓛 = P_Q.
Every equivariant map H_mark → Q is 𝓘 composed with a block scalar a Π₂ + b Π₁ + c Π₀ (Π_J the isotypic
projectors of V₁ ⊗ V₁): unique up to an independent factor on each J block, a phase each when isometric. -/

namespace Entropic.Pass2.Intertwiner
open Matrix

noncomputable section

def mulL {m k n : ℕ} (A : Fin m → Fin k → ℤ) (B : Fin k → Fin n → ℤ) : Fin m → Fin n → ℤ :=
  fun i j => (List.ofFn fun l => A i l * B l j).sum

theorem of_mul {m k n : ℕ} (A : Fin m → Fin k → ℤ) (B : Fin k → Fin n → ℤ) :
    Matrix.of A * Matrix.of B = Matrix.of (mulL A B) := by
  ext i j; simp [Matrix.mul_apply, mulL, List.sum_ofFn]

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
def MtF : Fin 16 → Fin 16 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0]]
def HmF : Fin 9 → Fin 9 → ℤ := ![![4, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -4]]
def PmF : Fin 9 → Fin 9 → ℤ := ![![0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0]]
def MmF : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 2, 0, 2, 0]]
/-- 12 𝓘. -/
def IF : Fin 16 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![-12, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -18, 0, -6, 0, 0, 0, 0, 0],
    ![0, 0, -19, 0, -8, 0, -1, 0, 0],
    ![12, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 6, 0, -6, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, -16, 0, -5, 0, 0],
    ![0, 0, 0, 0, 0, -27, 0, -9, 0],
    ![0, 6, 0, 18, 0, 0, 0, 0, 0],
    ![0, 0, 5, 0, 16, 0, -1, 0, 0],
    ![0, 0, 0, 0, 0, 12, 0, -12, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, -36],
    ![0, 0, 1, 0, 8, 0, 19, 0, 0],
    ![0, 0, 0, 0, 0, 9, 0, 27, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 36],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0]]
/-- 60 𝓛. -/
def LF : Fin 9 → Fin 16 → ℤ := ![![0, -30, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -33, 0, 0, 24, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -38, 0, 0, 16, 0, 0, -4, 0, 0, 2, 0, 0, 0],
    ![0, 0, 3, 0, 0, -24, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 5, 0, 0, -25, 0, 0, 25, 0, 0, -5, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -22, 0, 0, 12, 0, 0, -2, 0, 0],
    ![0, 0, 0, -2, 0, 0, 4, 0, 0, -16, 0, 0, 38, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -12, 0, 0, 22, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 10, 0]]
def YF : Fin 16 → Fin 16 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2880, 0, 0, -2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4608, 0, 0, -2304, 0, 0, -1152, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 5472, 0, 0, -864, 0, 0, -864, 0, 0, -288, 0, 0, 0],
    ![0, -2880, 0, 0, 2880, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -1728, 0, 0, 2304, 0, 0, -1728, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -864, 0, 0, 3168, 0, 0, -2592, 0, 0, -864, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 4608, 0, 0, -1728, 0, 0, -1152, 0, 0],
    ![0, 0, -1152, 0, 0, -2304, 0, 0, 4608, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, -864, 0, 0, -2592, 0, 0, 3168, 0, 0, -864, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -2304, 0, 0, 2304, 0, 0, -2304, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2880, 0, 0, -2880, 0],
    ![0, 0, 0, -288, 0, 0, -864, 0, 0, -864, 0, 0, 5472, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, -1152, 0, 0, -1728, 0, 0, 4608, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2880, 0, 0, 2880, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
theorem int_checks :
    (∀ i j, mulL HtF IF i j = mulL IF HmF i j) ∧ (∀ i j, mulL PtF IF i j = mulL IF PmF i j) ∧
    (∀ i j, mulL MtF IF i j = mulL IF MmF i j) ∧ (∀ i j, mulL YF IF i j = 5760 * IF i j) ∧
    (∀ i j, mulL LF IF i j = if i = j then 720 else 0) ∧ (∀ i j, 8 * mulL IF LF i j = YF i j) := by
  decide +kernel

/-- Y equals `AppP.Spin.Y` (5760 P_Q). -/
theorem YF_eq : ∀ i j, YF i j = Entropic.AppP.Spin.YF i j := by decide +kernel

abbrev cast {m n : ℕ} (A : Fin m → Fin n → ℤ) : Matrix (Fin m) (Fin n) ℂ := (Matrix.of A).map (Int.castRingHom ℂ)

theorem cast_mul {m k n : ℕ} (A : Fin m → Fin k → ℤ) (B : Fin k → Fin n → ℤ) :
    cast A * cast B = cast (mulL A B) := by
  rw [cast, cast, ← Matrix.map_mul, of_mul]

def Htc := cast HtF
def Ptc := cast PtF
def Mtc := cast MtF
def Hmc := cast HmF
def Pmc := cast PmF
def Mmc := cast MmF
def Ic : Matrix (Fin 16) (Fin 9) ℂ := (1/12 : ℂ) • cast IF
def Lc : Matrix (Fin 9) (Fin 16) ℂ := (1/60 : ℂ) • cast LF
def PQc : Matrix (Fin 16) (Fin 16) ℂ := (1/5760 : ℂ) • cast YF

theorem cast_ext {m n : ℕ} (A B : Fin m → Fin n → ℤ) (h : ∀ i j, A i j = B i j) : cast A = cast B := by
  ext i j; simp [h i j]

/-- C07-51 (existence): 𝓘 intertwines the total J_z, J₊, J₋ of V₁ ⊗ V₁ and V_{3/2} ⊗ V_{3/2}, has range in Q
(P_Q 𝓘 = 𝓘), and 𝓛𝓘 = I₉, 𝓘𝓛 = P_Q. -/
theorem intertwiner :
    Htc * Ic = Ic * Hmc ∧ Ptc * Ic = Ic * Pmc ∧ Mtc * Ic = Ic * Mmc ∧ PQc * Ic = Ic ∧ Lc * Ic = 1 ∧
      Ic * Lc = PQc := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := int_checks
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Htc, Ic, Hmc, Matrix.mul_smul, Matrix.smul_mul, cast_mul, cast_ext _ _ c1]
  · simp only [Ptc, Ic, Pmc, Matrix.mul_smul, Matrix.smul_mul, cast_mul, cast_ext _ _ c2]
  · simp only [Mtc, Ic, Mmc, Matrix.mul_smul, Matrix.smul_mul, cast_mul, cast_ext _ _ c3]
  · simp only [PQc, Ic, Matrix.mul_smul, Matrix.smul_mul, cast_mul, smul_smul]
    ext i j; simp [c4 i j]; ring
  · simp only [Lc, Ic, Matrix.mul_smul, Matrix.smul_mul, cast_mul, smul_smul]
    ext i j; simp [c5 i j, Matrix.one_apply]; split_ifs <;> norm_num
  · simp only [Lc, Ic, PQc, Matrix.mul_smul, Matrix.smul_mul, cast_mul, smul_smul]
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, eq_intCast]
    rw [← c6 i j]; push_cast; ring

def Pi2 : Matrix (Fin 9) (Fin 9) ℂ := Matrix.of ![![(1:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), ((1:ℂ)/2), (0:ℂ), ((1:ℂ)/2), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((1:ℂ)/6), (0:ℂ), ((1:ℂ)/3), (0:ℂ), ((1:ℂ)/6), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), ((1:ℂ)/2), (0:ℂ), ((1:ℂ)/2), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((1:ℂ)/3), (0:ℂ), ((2:ℂ)/3), (0:ℂ), ((1:ℂ)/3), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), ((1:ℂ)/2), (0:ℂ), ((1:ℂ)/2), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((1:ℂ)/6), (0:ℂ), ((1:ℂ)/3), (0:ℂ), ((1:ℂ)/6), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), ((1:ℂ)/2), (0:ℂ), ((1:ℂ)/2), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (1:ℂ)]]
def Pi1 : Matrix (Fin 9) (Fin 9) ℂ := Matrix.of ![![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), ((1:ℂ)/2), (0:ℂ), ((-1:ℂ)/2), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((1:ℂ)/2), (0:ℂ), (0:ℂ), (0:ℂ), ((-1:ℂ)/2), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), ((-1:ℂ)/2), (0:ℂ), ((1:ℂ)/2), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), ((1:ℂ)/2), (0:ℂ), ((-1:ℂ)/2), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((-1:ℂ)/2), (0:ℂ), (0:ℂ), (0:ℂ), ((1:ℂ)/2), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), ((-1:ℂ)/2), (0:ℂ), ((1:ℂ)/2), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)]]
def Pi0 : Matrix (Fin 9) (Fin 9) ℂ := Matrix.of ![![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((1:ℂ)/3), (0:ℂ), ((-1:ℂ)/3), (0:ℂ), ((1:ℂ)/3), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((-1:ℂ)/3), (0:ℂ), ((1:ℂ)/3), (0:ℂ), ((-1:ℂ)/3), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), ((1:ℂ)/3), (0:ℂ), ((-1:ℂ)/3), (0:ℂ), ((1:ℂ)/3), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)],
    ![(0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ), (0:ℂ)]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The commutant of the total J_z, J₊ on V₁ ⊗ V₁ is spanned by Π₂, Π₁, Π₀. -/
theorem mark_commutant (X : Matrix (Fin 9) (Fin 9) ℂ) (h1 : X * Hmc = Hmc * X) (h2 : X * Pmc = Pmc * X) :
    X = ((1:ℂ) * X 0 0) • Pi2 + ((-1:ℂ) * X 0 0 + (2:ℂ) * X 1 1) • Pi1 + ((1:ℂ) * X 0 0 + (-3:ℂ) * X 1 1 + (3:ℂ) * X 2 2) • Pi0 := by
  simp only [Hmc, Pmc, cast] at h1 h2
  have f_0_1 : X 0 1 = 0 := by
      have q0 := congrFun (congrFun h1 0) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_0_2 : X 0 2 = 0 := by
      have q0 := congrFun (congrFun h1 0) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_0_3 : X 0 3 = 0 := by
      have q0 := congrFun (congrFun h1 0) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_0_4 : X 0 4 = 0 := by
      have q0 := congrFun (congrFun h1 0) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_0_5 : X 0 5 = 0 := by
      have q0 := congrFun (congrFun h1 0) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_0_6 : X 0 6 = 0 := by
      have q0 := congrFun (congrFun h1 0) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_0_7 : X 0 7 = 0 := by
      have q0 := congrFun (congrFun h1 0) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_0_8 : X 0 8 = 0 := by
      have q0 := congrFun (congrFun h1 0) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/8) * q0
  have f_1_0 : X 1 0 = 0 := by
      have q0 := congrFun (congrFun h1 1) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_1_2 : X 1 2 = 0 := by
      have q0 := congrFun (congrFun h1 1) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_1_4 : X 1 4 = 0 := by
      have q0 := congrFun (congrFun h1 1) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_1_5 : X 1 5 = 0 := by
      have q0 := congrFun (congrFun h1 1) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_1_6 : X 1 6 = 0 := by
      have q0 := congrFun (congrFun h1 1) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_1_7 : X 1 7 = 0 := by
      have q0 := congrFun (congrFun h1 1) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_1_8 : X 1 8 = 0 := by
      have q0 := congrFun (congrFun h1 1) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_2_0 : X 2 0 = 0 := by
      have q0 := congrFun (congrFun h1 2) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_2_1 : X 2 1 = 0 := by
      have q0 := congrFun (congrFun h1 2) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_2_3 : X 2 3 = 0 := by
      have q0 := congrFun (congrFun h1 2) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_2_5 : X 2 5 = 0 := by
      have q0 := congrFun (congrFun h1 2) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_2_7 : X 2 7 = 0 := by
      have q0 := congrFun (congrFun h1 2) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_2_8 : X 2 8 = 0 := by
      have q0 := congrFun (congrFun h1 2) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_3_0 : X 3 0 = 0 := by
      have q0 := congrFun (congrFun h1 3) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_3_1 : X 3 1 = (1:ℂ) * X 0 0 + (-1:ℂ) * X 1 1 := by
      have q0 := congrFun (congrFun h2 0) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (-1:ℂ) * q0
  have f_3_2 : X 3 2 = 0 := by
      have q0 := congrFun (congrFun h1 3) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_4 : X 3 4 = 0 := by
      have q0 := congrFun (congrFun h1 3) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_5 : X 3 5 = 0 := by
      have q0 := congrFun (congrFun h1 3) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_3_6 : X 3 6 = 0 := by
      have q0 := congrFun (congrFun h1 3) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_3_7 : X 3 7 = 0 := by
      have q0 := congrFun (congrFun h1 3) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_3_8 : X 3 8 = 0 := by
      have q0 := congrFun (congrFun h1 3) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/6) * q0
  have f_4_0 : X 4 0 = 0 := by
      have q0 := congrFun (congrFun h1 4) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_4_1 : X 4 1 = 0 := by
      have q0 := congrFun (congrFun h1 4) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_4_2 : X 4 2 = (1:ℂ) * X 1 1 + (-1:ℂ) * X 2 2 := by
      have q0 := congrFun (congrFun h2 1) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (-1:ℂ) * q0
  have f_4_3 : X 4 3 = 0 := by
      have q0 := congrFun (congrFun h1 4) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_4_5 : X 4 5 = 0 := by
      have q0 := congrFun (congrFun h1 4) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_4_7 : X 4 7 = 0 := by
      have q0 := congrFun (congrFun h1 4) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_4_8 : X 4 8 = 0 := by
      have q0 := congrFun (congrFun h1 4) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_5_0 : X 5 0 = 0 := by
      have q0 := congrFun (congrFun h1 5) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_5_1 : X 5 1 = 0 := by
      have q0 := congrFun (congrFun h1 5) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_5_2 : X 5 2 = 0 := by
      have q0 := congrFun (congrFun h1 5) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_3 : X 5 3 = 0 := by
      have q0 := congrFun (congrFun h1 5) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_5_4 : X 5 4 = 0 := by
      have q0 := congrFun (congrFun h1 5) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_6 : X 5 6 = 0 := by
      have q0 := congrFun (congrFun h1 5) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_5_8 : X 5 8 = 0 := by
      have q0 := congrFun (congrFun h1 5) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_6_0 : X 6 0 = 0 := by
      have q0 := congrFun (congrFun h1 6) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_6_1 : X 6 1 = 0 := by
      have q0 := congrFun (congrFun h1 6) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_6_2 : X 6 2 = (1:ℂ) * X 0 0 + (-2:ℂ) * X 1 1 + (1:ℂ) * X 2 2 := by
      have q0 := congrFun (congrFun h2 1) 2
      have q1 := congrFun (congrFun h2 3) 2
      have q2 := congrFun (congrFun h2 0) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (1:ℂ) * q0 + (-1:ℂ) * q1 + (-1:ℂ) * q2
  have f_6_3 : X 6 3 = 0 := by
      have q0 := congrFun (congrFun h1 6) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_6_5 : X 6 5 = 0 := by
      have q0 := congrFun (congrFun h1 6) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_6_7 : X 6 7 = 0 := by
      have q0 := congrFun (congrFun h1 6) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_6_8 : X 6 8 = 0 := by
      have q0 := congrFun (congrFun h1 6) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/4) * q0
  have f_7_0 : X 7 0 = 0 := by
      have q0 := congrFun (congrFun h1 7) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_7_1 : X 7 1 = 0 := by
      have q0 := congrFun (congrFun h1 7) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_7_2 : X 7 2 = 0 := by
      have q0 := congrFun (congrFun h1 7) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_7_3 : X 7 3 = 0 := by
      have q0 := congrFun (congrFun h1 7) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_7_4 : X 7 4 = 0 := by
      have q0 := congrFun (congrFun h1 7) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_7_6 : X 7 6 = 0 := by
      have q0 := congrFun (congrFun h1 7) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_7_8 : X 7 8 = 0 := by
      have q0 := congrFun (congrFun h1 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * q0
  have f_8_0 : X 8 0 = 0 := by
      have q0 := congrFun (congrFun h1 8) 0
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/8) * q0
  have f_8_1 : X 8 1 = 0 := by
      have q0 := congrFun (congrFun h1 8) 1
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_8_2 : X 8 2 = 0 := by
      have q0 := congrFun (congrFun h1 8) 2
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_8_3 : X 8 3 = 0 := by
      have q0 := congrFun (congrFun h1 8) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/6) * q0
  have f_8_4 : X 8 4 = 0 := by
      have q0 := congrFun (congrFun h1 8) 4
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_8_5 : X 8 5 = 0 := by
      have q0 := congrFun (congrFun h1 8) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_8_6 : X 8 6 = 0 := by
      have q0 := congrFun (congrFun h1 8) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/4) * q0
  have f_8_7 : X 8 7 = 0 := by
      have q0 := congrFun (congrFun h1 8) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/2) * q0
  have f_4_4 : X 4 4 = (1:ℂ) * X 0 0 + (-1:ℂ) * X 1 1 + (1:ℂ) * X 2 2 := by
      have q1 := congrFun (congrFun h2 1) 4
      have q2 := congrFun (congrFun h2 2) 5
      have q3 := congrFun (congrFun h2 6) 5
      have q4 := congrFun (congrFun h2 3) 4
      have q6 := congrFun (congrFun h2 4) 5
      have q7 := congrFun (congrFun h2 0) 3
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/3) * f_6_2 + ((-1:ℂ)/3) * q1 + ((-1:ℂ)/3) * q2 + ((-1:ℂ)/3) * q3 + ((-1:ℂ)/3) * q4 + ((1:ℂ)/3) * f_3_1 + ((1:ℂ)/3) * q6 + ((-1:ℂ)/3) * q7 + ((-1:ℂ)/3) * f_4_2
  have f_4_6 : X 4 6 = (1:ℂ) * X 1 1 + (-1:ℂ) * X 2 2 := by
      have q0 := congrFun (congrFun h2 3) 6
      have q1 := congrFun (congrFun h2 2) 7
      have q2 := congrFun (congrFun h2 2) 5
      have q3 := congrFun (congrFun h2 1) 6
      have q4 := congrFun (congrFun h2 0) 3
      have q6 := congrFun (congrFun h2 4) 7
      have q7 := congrFun (congrFun h2 6) 5
      have q8 := congrFun (congrFun h2 6) 7
      have q9 := congrFun (congrFun h2 4) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * q1 + ((1:ℂ)/3) * q2 + ((-1:ℂ)/3) * q3 + ((-1:ℂ)/3) * q4 + ((-1:ℂ)/3) * f_6_2 + ((1:ℂ)/3) * q6 + ((1:ℂ)/3) * q7 + ((-1:ℂ)/3) * q8 + ((-1:ℂ)/3) * q9 + ((1:ℂ)/3) * f_4_2
  have f_5_7 : X 5 7 = (1:ℂ) * X 0 0 + (-1:ℂ) * X 1 1 := by
      have q1 := congrFun (congrFun h2 2) 7
      have q2 := congrFun (congrFun h2 2) 5
      have q3 := congrFun (congrFun h2 1) 6
      have q4 := congrFun (congrFun h2 0) 3
      have q5 := congrFun (congrFun h2 3) 4
      have q7 := congrFun (congrFun h2 5) 8
      have q8 := congrFun (congrFun h2 7) 8
      have q9 := congrFun (congrFun h2 4) 7
      have q10 := congrFun (congrFun h2 6) 5
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((1:ℂ)/3) * f_6_2 + ((-1:ℂ)/3) * q1 + ((1:ℂ)/3) * q2 + ((-1:ℂ)/3) * q3 + ((-1:ℂ)/3) * q4 + ((-1:ℂ)/3) * q5 + ((1:ℂ)/3) * f_3_1 + ((1:ℂ)/3) * q7 + ((-1:ℂ)/3) * q8 + ((-1:ℂ)/3) * q9 + ((-1:ℂ)/3) * q10
  have f_7_7 : X 7 7 = (1:ℂ) * X 1 1 := by
      have q0 := congrFun (congrFun h2 0) 3
      have q2 := congrFun (congrFun h2 1) 4
      have q3 := congrFun (congrFun h2 2) 5
      have q4 := congrFun (congrFun h2 3) 6
      have q5 := congrFun (congrFun h2 5) 8
      have q6 := congrFun (congrFun h2 6) 5
      have q7 := congrFun (congrFun h2 6) 7
      have q8 := congrFun (congrFun h2 7) 8
      have q9 := congrFun (congrFun h2 4) 7
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/3) * q0 + ((-1:ℂ)/3) * f_6_2 + ((-1:ℂ)/3) * q2 + ((-1:ℂ)/3) * q3 + ((-1:ℂ)/3) * q4 + ((-1:ℂ)/3) * q5 + ((1:ℂ)/3) * q6 + ((-1:ℂ)/3) * q7 + ((1:ℂ)/3) * q8 + ((-1:ℂ)/3) * q9
  have f_1_3 : X 1 3 = (1:ℂ) * X 0 0 + (-1:ℂ) * X 1 1 := by
      have q2 := congrFun (congrFun h2 3) 6
      have q3 := congrFun (congrFun h2 0) 3
      have q5 := congrFun (congrFun h2 5) 8
      have q6 := congrFun (congrFun h2 2) 7
      have q7 := congrFun (congrFun h2 2) 5
      have q8 := congrFun (congrFun h2 1) 6
      have q9 := congrFun (congrFun h2 6) 5
      have q10 := congrFun (congrFun h2 6) 7
      have q11 := congrFun (congrFun h2 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (-1:ℂ) * f_7_7 + (1:ℂ) * f_5_7 + ((-1:ℂ)/2) * q2 + ((-1:ℂ)/2) * q3 + ((-1:ℂ)/2) * f_6_2 + ((-1:ℂ)/2) * q5 + ((1:ℂ)/2) * q6 + ((-1:ℂ)/2) * q7 + ((1:ℂ)/2) * q8 + ((1:ℂ)/2) * q9 + ((-1:ℂ)/2) * q10 + ((1:ℂ)/2) * q11
  have f_2_4 : X 2 4 = (1:ℂ) * X 1 1 + (-1:ℂ) * X 2 2 := by
      have q1 := congrFun (congrFun h2 3) 6
      have q2 := congrFun (congrFun h2 2) 7
      have q3 := congrFun (congrFun h2 1) 6
      have q4 := congrFun (congrFun h2 0) 3
      have q7 := congrFun (congrFun h2 5) 8
      have q8 := congrFun (congrFun h2 2) 5
      have q9 := congrFun (congrFun h2 6) 5
      have q10 := congrFun (congrFun h2 6) 7
      have q11 := congrFun (congrFun h2 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (1:ℂ) * f_7_7 + ((1:ℂ)/2) * q1 + ((1:ℂ)/2) * q2 + ((1:ℂ)/2) * q3 + ((1:ℂ)/2) * q4 + (1:ℂ) * f_4_6 + ((1:ℂ)/2) * f_6_2 + ((1:ℂ)/2) * q7 + ((1:ℂ)/2) * q8 + ((-1:ℂ)/2) * q9 + ((1:ℂ)/2) * q10 + ((-1:ℂ)/2) * q11
  have f_3_3 : X 3 3 = (1:ℂ) * X 1 1 := by
      have q2 := congrFun (congrFun h2 3) 6
      have q4 := congrFun (congrFun h2 5) 8
      have q5 := congrFun (congrFun h2 2) 7
      have q6 := congrFun (congrFun h2 2) 5
      have q7 := congrFun (congrFun h2 1) 6
      have q8 := congrFun (congrFun h2 0) 3
      have q9 := congrFun (congrFun h2 6) 5
      have q10 := congrFun (congrFun h2 6) 7
      have q11 := congrFun (congrFun h2 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (1:ℂ) * f_7_7 + (-1:ℂ) * f_5_7 + ((1:ℂ)/2) * q2 + ((1:ℂ)/2) * f_6_2 + ((1:ℂ)/2) * q4 + ((-1:ℂ)/2) * q5 + ((1:ℂ)/2) * q6 + ((-1:ℂ)/2) * q7 + ((-1:ℂ)/2) * q8 + ((-1:ℂ)/2) * q9 + ((1:ℂ)/2) * q10 + ((-1:ℂ)/2) * q11
  have f_5_5 : X 5 5 = (1:ℂ) * X 1 1 := by
      have q1 := congrFun (congrFun h2 3) 6
      have q2 := congrFun (congrFun h2 2) 7
      have q3 := congrFun (congrFun h2 2) 5
      have q4 := congrFun (congrFun h2 1) 6
      have q5 := congrFun (congrFun h2 0) 3
      have q8 := congrFun (congrFun h2 5) 8
      have q9 := congrFun (congrFun h2 6) 5
      have q10 := congrFun (congrFun h2 6) 7
      have q11 := congrFun (congrFun h2 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (1:ℂ) * f_7_7 + ((1:ℂ)/2) * q1 + ((1:ℂ)/2) * q2 + ((-1:ℂ)/2) * q3 + ((1:ℂ)/2) * q4 + ((1:ℂ)/2) * q5 + (1:ℂ) * f_4_6 + ((1:ℂ)/2) * f_6_2 + ((1:ℂ)/2) * q8 + ((-1:ℂ)/2) * q9 + ((1:ℂ)/2) * q10 + ((-1:ℂ)/2) * q11
  have f_6_4 : X 6 4 = (1:ℂ) * X 1 1 + (-1:ℂ) * X 2 2 := by
      have q2 := congrFun (congrFun h2 5) 8
      have q3 := congrFun (congrFun h2 3) 6
      have q4 := congrFun (congrFun h2 2) 7
      have q5 := congrFun (congrFun h2 2) 5
      have q6 := congrFun (congrFun h2 1) 6
      have q7 := congrFun (congrFun h2 0) 3
      have q9 := congrFun (congrFun h2 6) 5
      have q10 := congrFun (congrFun h2 6) 7
      have q11 := congrFun (congrFun h2 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) ((-1:ℂ)/2) * f_6_2 + (1:ℂ) * f_5_7 + ((-1:ℂ)/2) * q2 + ((1:ℂ)/2) * q3 + ((1:ℂ)/2) * q4 + ((-1:ℂ)/2) * q5 + ((1:ℂ)/2) * q6 + ((1:ℂ)/2) * q7 + (1:ℂ) * f_4_6 + ((1:ℂ)/2) * q9 + ((1:ℂ)/2) * q10 + ((1:ℂ)/2) * q11
  have f_7_5 : X 7 5 = (1:ℂ) * X 0 0 + (-1:ℂ) * X 1 1 := by
      have q1 := congrFun (congrFun h2 5) 8
      have q2 := congrFun (congrFun h2 3) 6
      have q3 := congrFun (congrFun h2 2) 7
      have q4 := congrFun (congrFun h2 2) 5
      have q5 := congrFun (congrFun h2 1) 6
      have q6 := congrFun (congrFun h2 0) 3
      have q9 := congrFun (congrFun h2 6) 5
      have q10 := congrFun (congrFun h2 6) 7
      have q11 := congrFun (congrFun h2 7) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (1:ℂ) * f_5_7 + ((-1:ℂ)/2) * q1 + ((1:ℂ)/2) * q2 + ((1:ℂ)/2) * q3 + ((-1:ℂ)/2) * q4 + ((1:ℂ)/2) * q5 + ((1:ℂ)/2) * q6 + (1:ℂ) * f_4_6 + ((1:ℂ)/2) * f_6_2 + ((-1:ℂ)/2) * q9 + ((1:ℂ)/2) * q10 + ((1:ℂ)/2) * q11
  have f_2_6 : X 2 6 = (1:ℂ) * X 0 0 + (-2:ℂ) * X 1 1 + (1:ℂ) * X 2 2 := by
      have q0 := congrFun (congrFun h2 1) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (-1:ℂ) * q0 + (1:ℂ) * f_1_3 + (-1:ℂ) * f_4_6
  have f_6_6 : X 6 6 = (1:ℂ) * X 2 2 := by
      have q0 := congrFun (congrFun h2 3) 6
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (-1:ℂ) * q0 + (1:ℂ) * f_3_3 + (-1:ℂ) * f_4_6
  have f_8_8 : X 8 8 = (1:ℂ) * X 0 0 := by
      have q0 := congrFun (congrFun h2 5) 8
      linear_combination (norm := (simp [Matrix.mul_apply, Fin.sum_univ_succ, Hmc, Pmc, HmF, PmF] <;> ring_nf)) (-1:ℂ) * q0 + (1:ℂ) * f_5_5 + (1:ℂ) * f_5_7
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Pi2, Pi1, Pi0, f_0_1, f_0_2, f_0_3, f_0_4, f_0_5, f_0_6, f_0_7, f_0_8, f_1_0, f_1_2, f_1_4, f_1_5, f_1_6, f_1_7, f_1_8, f_2_0, f_2_1, f_2_3, f_2_5, f_2_7, f_2_8, f_3_0, f_3_1, f_3_2, f_3_4, f_3_5, f_3_6, f_3_7, f_3_8, f_4_0, f_4_1, f_4_2, f_4_3, f_4_5, f_4_7, f_4_8, f_5_0, f_5_1, f_5_2, f_5_3, f_5_4, f_5_6, f_5_8, f_6_0, f_6_1, f_6_2, f_6_3, f_6_5, f_6_7, f_6_8, f_7_0, f_7_1, f_7_2, f_7_3, f_7_4, f_7_6, f_7_8, f_8_0, f_8_1, f_8_2, f_8_3, f_8_4, f_8_5, f_8_6, f_8_7, f_4_4, f_4_6, f_5_7, f_7_7, f_1_3, f_2_4, f_3_3, f_5_5, f_6_4, f_7_5, f_2_6, f_6_6, f_8_8] <;> (try ring_nf)

/-- C07-51 (uniqueness): an equivariant map 𝓙 : H_mark → V_{3/2} ⊗ V_{3/2} with range in Q equals
𝓘 (a Π₂ + b Π₁ + c Π₀). -/
theorem intertwiner_unique (J : Matrix (Fin 16) (Fin 9) ℂ) (h1 : Htc * J = J * Hmc) (h2 : Ptc * J = J * Pmc)
    (hQ : PQc * J = J) : ∃ a b c : ℂ, J = Ic * (a • Pi2 + b • Pi1 + c • Pi0) := by
  obtain ⟨i1, i2, -, -, il, li⟩ := intertwiner
  set X := Lc * J with hX
  have hJ : J = Ic * X := by rw [hX, ← Matrix.mul_assoc, li, hQ]
  have comm : ∀ (A : Matrix (Fin 16) (Fin 16) ℂ) (B : Matrix (Fin 9) (Fin 9) ℂ), A * Ic = Ic * B →
      A * J = J * B → X * B = B * X := by
    intro A B hAI hAJ
    calc X * B = Lc * (J * B) := by rw [hX, Matrix.mul_assoc]
      _ = Lc * (A * J) := by rw [hAJ]
      _ = Lc * (A * (Ic * X)) := by rw [← hJ]
      _ = Lc * (Ic * B * X) := by rw [← Matrix.mul_assoc A, hAI, Matrix.mul_assoc]
      _ = B * X := by rw [← Matrix.mul_assoc Lc (Ic * B) X, ← Matrix.mul_assoc Lc Ic B, il, Matrix.one_mul]
  have hX1 := comm _ _ i1 h1
  have hX2 := comm _ _ i2 h2
  exact ⟨_, _, _, by rw [hJ, mark_commutant X hX1 hX2]⟩

end

end Entropic.Pass2.Intertwiner
