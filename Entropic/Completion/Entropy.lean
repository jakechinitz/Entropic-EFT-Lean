import Entropic.Completion.InfiniteHistory
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Connect the entropy of the actual infinite-history marginal to the native
gshare used by the G* formula. Product marginalization follows the existing
Entropic/AppCDE/Information.lean proof, reproduced here for the 4.19 checker.
This establishes the Shannon/determinant mathematics, not the physical
assignment of the determinant line to a charged rest-energy gap. -/
noncomputable section
open scoped BigOperators
namespace Entropic.Completion.Entropy
open Entropic.Compatibility.GibbsHistory Entropic.ClosureRoot

def H {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) := -∑ s, p s*Real.log (p s)

theorem native_entropy (eta : ℝ) : H (probability eta)=gshare eta := by
  unfold H
  rw [Fintype.sum_sigma]
  simp only [probability, weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [probability,weight,level,Entropic.Compatibility.GibbsHistory.multiplicity,gshare,specR,Fin.sum_univ_succ,nsmul_eq_mul]

-- Adapted proof of the already established product-marginal identity.
theorem product_marginal {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ}
    (p : Ω → ℝ) (hp : ∑ s,p s=1) (i : Fin n) (g : Ω → ℝ) :
    ∑ x : Fin n → Ω, (∏ j,p (x j))*g (x i)=∑ s,p s*g s := by
  have eqv : ∀ x : Fin n → Ω, (∏ j,p (x j))*g (x i)=
      ∏ j,(p (x j)*(if j=i then g (x j) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib,Finset.prod_ite_eq' Finset.univ i,if_pos (Finset.mem_univ _)]
  simp_rw [eqv]
  rw [← Fintype.piFinset_univ,← Finset.prod_univ_sum (t:=fun _ => Finset.univ)
    (f:=fun j s => p s*(if j=i then g s else 1))]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp only [hj,if_false,mul_one]; exact hp
  · simp

theorem block_entropy (eta : ℝ) (n : ℕ) :
    H (fun x : Fin n → Microstate => ∏ i,probability eta (x i))=n*gshare eta := by
  have hlog : ∀ x : Fin n → Microstate,
      Real.log (∏ i,probability eta (x i))=∑ i,Real.log (probability eta (x i)) := by
    intro x; exact Real.log_prod (s := Finset.univ) (f := fun i => probability eta (x i)) (fun i _ => (probability_positive eta (x i)).ne')
  unfold H
  simp_rw [hlog,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm : ∀ i : Fin n, (∑ x : Fin n → Microstate,
      (∏ j,probability eta (x j))*Real.log (probability eta (x i)))=
      ∑ s,probability eta s*Real.log (probability eta s) := fun i =>
    product_marginal (probability eta) (probability_normalized eta) i (fun s => Real.log (probability eta s))
  simp_rw [hm]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← native_entropy]
  dsimp [H]; ring

theorem entropy_per_tick (eta : ℝ) (n : ℕ) (hn : 0<n) :
    H (fun x : Fin n → Microstate => ∏ i,probability eta (x i))/(n:ℝ)=gshare eta := by
  rw [block_entropy]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

theorem seven_channel_determinant (eta : ℝ) :
    Real.exp (-H (fun x : Fin 7 → Microstate => ∏ i,probability eta (x i)))=
      Real.exp (-7*gshare eta) := by
  rw [block_entropy]; norm_num

end Entropic.Completion.Entropy
