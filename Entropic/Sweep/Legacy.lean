import Entropic.Sweep.Spin
import Entropic.EFT.Representation.SharpTransfer
import Entropic.EFT.Scale.Leptons
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Chunk 14: instances of two typed certificate structures of the v0.8 library
(`OrthogonalComplementSplit`, `OrderedPairCountMath`), proved from the spin-3/2 projectors. -/

noncomputable section
namespace Entropic.Sweep.Legacy
open Matrix Entropic.AppP.Spin Entropic.Sweep.SpinPair

abbrev ψc : Matrix (Fin 16) (Fin 16) ℤ →+* Matrix (Fin 16) (Fin 16) ℂ := (Int.castRingHom ℂ).mapMatrix

def P3c : Matrix (Fin 16) (Fin 16) ℂ := (1/5760 : ℂ) • ψc L0
def PQc : Matrix (Fin 16) (Fin 16) ℂ := (1/5760 : ℂ) • ψc Y

theorem ψc_smul (k : ℤ) (A : Matrix (Fin 16) (Fin 16) ℤ) : ψc (k • A) = (k : ℂ) • ψc A := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, eq_intCast]

theorem split_c : P3c + PQc = 1 ∧ P3c * PQc = 0 ∧ PQc * P3c = 0 ∧ P3c * P3c = P3c ∧ PQc * PQc = PQc := by
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := projector_split
  have m : ∀ A B : Matrix (Fin 16) (Fin 16) ℤ, ((1/5760 : ℂ) • ψc A) * ((1/5760 : ℂ) • ψc B) =
      (1/5760 * (1/5760) : ℂ) • ψc (A * B) := by
    intro A B; rw [map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg ψc h1
    rw [map_add, ψc_smul, map_one] at this
    simp only [P3c, PQc, ← smul_add, add_comm (ψc L0), this, smul_smul]; norm_num
  · simp only [P3c, PQc, m, h3, map_zero, smul_zero]
  · simp only [P3c, PQc, m, h2, map_zero, smul_zero]
  · simp only [P3c, m, h4, ψc_smul, smul_smul]; norm_num
  · simp only [PQc, m, h5, ψc_smul, smul_smul]; norm_num

abbrev E16 := EuclideanSpace ℂ (Fin 16)

theorem toE_mul (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) = Matrix.toEuclideanLin (A * B) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.toLin_mul]

/-- The v0.8 interface `OrthogonalComplementSplit` instantiated on C¹⁶ = V_{3/2} ⊗ V_{3/2} by the
spin-3 projector P₃ and its complement P_Q (the sharp 16 = 7 + 9 split). -/
def sharpSplit : Entropic.EFT.Representation.OrthogonalComplementSplit E16 where
  P := Matrix.toEuclideanLin P3c
  Q := Matrix.toEuclideanLin PQc
  p_add_q := by rw [← map_add, split_c.1, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_one]
  pq_zero := by rw [toE_mul, split_c.2.1, map_zero]
  qp_zero := by rw [toE_mul, split_c.2.2.1, map_zero]
  p_idem := by rw [toE_mul, split_c.2.2.2.1]
  q_idem := by rw [toE_mul, split_c.2.2.2.2]

/-- The v0.8 interface `OrderedPairCountMath`: N² = N + 2·C(N, 2). -/
theorem orderedPairs : Entropic.EFT.Scale.OrderedPairCountMath where
  identity := by
    intro N; induction N with
    | zero => simp
    | succ n ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith [ih]

end Entropic.Sweep.Legacy
