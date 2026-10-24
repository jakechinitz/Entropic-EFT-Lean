import Mathlib

/-! The quadratic Maxwell symbol in three spatial dimensions. This is a finite
linear-algebra result, not a proof of a Coulomb phase of an interacting model. -/
noncomputable section
open scoped BigOperators
namespace Entropic.Electromagnetism

def pairing (s v : Fin 3 → ℂ) : ℂ := ∑ i, star (s i)*v i
def symbolNorm (s : Fin 3 → ℂ) : ℂ := pairing s s
def maxwellSymbol (s v : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  symbolNorm s*v i-s i*pairing s v

theorem symbol_norm_as_sum (s : Fin 3 → ℂ) :
    symbolNorm s = ((∑ i, Complex.normSq (s i) : ℝ) : ℂ) := by
  simp only [symbolNorm, pairing, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Complex.normSq_eq_conj_mul_self.symm

theorem nonzero_symbol_norm (s : Fin 3 → ℂ) (hs : s ≠ 0) : symbolNorm s ≠ 0 := by
  intro h
  rw [symbol_norm_as_sum] at h
  have hz : ∑ i, Complex.normSq (s i)=0 := by exact_mod_cast h
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => Complex.normSq_nonneg (s i))).mp hz
  apply hs
  funext i
  exact Complex.normSq_eq_zero.mp (hall i (Finset.mem_univ i))

theorem longitudinal_kernel (s : Fin 3 → ℂ) : maxwellSymbol s s=0 := by
  funext i
  simp [maxwellSymbol, symbolNorm, mul_comm]

theorem transverse_eigenvalue (s v : Fin 3 → ℂ) (ht : pairing s v=0) :
    maxwellSymbol s v = symbolNorm s • v := by
  funext i
  simp [maxwellSymbol, ht]

theorem symbol_output_transverse (s v : Fin 3 → ℂ) :
    pairing s (maxwellSymbol s v)=0 := by
  simp only [pairing, maxwellSymbol, symbolNorm, Fin.sum_univ_succ]
  ring

theorem symbol_polynomial (s v : Fin 3 → ℂ) :
    maxwellSymbol s (maxwellSymbol s v)=symbolNorm s • maxwellSymbol s v :=
  transverse_eigenvalue s _ (symbol_output_transverse s v)

def transverseFunctional (s : Fin 3 → ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun := pairing s
  map_add' := by intro v w; simp [pairing, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    simp [pairing, Finset.mul_sum, mul_left_comm]

theorem transverse_functional_nonzero (s : Fin 3 → ℂ) (hs : s ≠ 0) :
    transverseFunctional s ≠ 0 := by
  intro h
  apply hs
  funext i
  have hi := congrArg (fun f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ => f (Pi.single i 1)) h
  fin_cases i <;> simpa [transverseFunctional, pairing, Fin.sum_univ_succ,
    Pi.single_apply, star_eq_zero] using hi

theorem two_transverse_dimensions (s : Fin 3 → ℂ) (hs : s ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (transverseFunctional s))=2 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (transverse_functional_nonzero s hs)
  have hd : Module.finrank ℂ (Fin 3 → ℂ)=3 := by simp
  omega

theorem nonzero_norm_kernel_is_longitudinal (s v : Fin 3 → ℂ)
    (hn : symbolNorm s ≠ 0) (hv : maxwellSymbol s v=0) :
    v = (pairing s v / symbolNorm s) • s := by
  funext i
  have h := congrFun hv i
  simp only [maxwellSymbol, Pi.zero_apply] at h
  change v i = (pairing s v / symbolNorm s)*s i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hn).2
  have he := sub_eq_zero.mp h
  simpa [mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div] using he

theorem real_link_symbol (x : ℝ) :
    (Real.cos x-1)^2+(Real.sin x)^2=4*(Real.sin (x/2))^2 := by
  have h := Real.sin_sq_add_cos_sq x
  have hh := Real.cos_two_mul (x/2)
  rw [show 2*(x/2)=x by ring] at hh
  nlinarith [Real.sin_sq_add_cos_sq (x/2)]

theorem low_momentum_component :
    HasDerivAt (fun k : ℝ => 2*Real.sin (k/2)) 1 0 := by
  convert ((Real.hasDerivAt_sin (0/2)).comp 0 ((hasDerivAt_id (0:ℝ)).div_const 2)).const_mul 2 using 1 <;> norm_num

end Entropic.Electromagnetism
