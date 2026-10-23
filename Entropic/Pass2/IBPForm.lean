import Entropic.Pass2.Fields

/-! Second pass, chunk 16: C11-52 (first part). The pointwise identity
4φΔψ + 4ψΔψ + 6|∇ψ|² = 2(|∇ψ|² − 2∇φ·∇ψ) + div(4φ∇ψ + 4ψ∇ψ),
so the two sides agree up to a total divergence. -/

namespace Entropic.Var

variable {n : ℕ}

/-- C11-52: the quadratic form after integration by parts, with the explicit divergence. -/
theorem quad_form_ibp {φ ψ : E n → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (x : E n) :
    4 * φ x * lap ψ x + 4 * ψ x * lap ψ x + 6 * ∑ i, pd ψ i x ^ 2 =
      2 * (∑ i, pd ψ i x ^ 2 - 2 * ∑ i, pd φ i x * pd ψ i x) +
        dvg (fun i y => 4 * (φ y * pd ψ i y) + 4 * (ψ y * pd ψ i y)) x := by
  have hφ1 := diff_of_c1 (c1_of_c2 hφ)
  have hψ1 := diff_of_c1 (c1_of_c2 hψ)
  have hd : ∀ i, Differentiable ℝ (pd ψ i) := fun i => diff_of_c1 (pd_c1 hψ i)
  have e1 : dvg (fun i y => φ y * pd ψ i y) x = ∑ i, (pd φ i x * pd ψ i x + φ x * pd (pd ψ i) i x) :=
    Finset.sum_congr rfl fun i _ => pd_mul hφ1 (hd i) i x
  have e2 : dvg (fun i y => ψ y * pd ψ i y) x = ∑ i, (pd ψ i x * pd ψ i x + ψ x * pd (pd ψ i) i x) :=
    Finset.sum_congr rfl fun i _ => pd_mul hψ1 (hd i) i x
  rw [dvg_lin 4 4 (A := fun i y => φ y * pd ψ i y) (B := fun i y => ψ y * pd ψ i y)
    (fun i => hφ1.mul (hd i)) (fun i => hψ1.mul (hd i)), e1, e2]
  simp only [lap, dvg, Finset.sum_add_distrib, ← Finset.mul_sum, sq]
  ring

end Entropic.Var
