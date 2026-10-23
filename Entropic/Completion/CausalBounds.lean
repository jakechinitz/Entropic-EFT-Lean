import Mathlib

/-! A candidate discrete invariant-domain repair, not the paper's unmodified
telegrapher equation and not a derived horizon boundary action. Each tick has
one-cell range, preserves [0,1], and permits a nonzero bounded depletion. -/
noncomputable section
namespace Entropic.Completion.CausalBounds

def update (a d : ℝ) (q : ℤ → ℝ) (i : ℤ) :=
  (1-d)*((1-a)*q i+(a/2)*(q (i-1)+q (i+1)))

theorem invariant_step (a d : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (q : ℤ → ℝ) (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1) (i : ℤ) :
    0 ≤ update a d q i ∧ update a d q i ≤ 1 := by
  obtain ⟨h0,h1⟩ := hq i
  obtain ⟨hl0,hl1⟩ := hq (i-1)
  obtain ⟨hr0,hr1⟩ := hq (i+1)
  have hcomp : 0 ≤ 1-a := sub_nonneg.mpr ha1
  have hc0 : 0 ≤ (1-a)*q i+(a/2)*(q (i-1)+q (i+1)) := by positivity
  have hc1 : (1-a)*q i+(a/2)*(q (i-1)+q (i+1)) ≤ 1 := by
    have hself := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ha1)
    have hneigh := mul_le_mul_of_nonneg_left (show q (i-1)+q (i+1) ≤ 2 by linarith) (show 0 ≤ a/2 by positivity)
    nlinarith
  dsimp [update]
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hd1) hc0
  · have hh := mul_le_mul_of_nonneg_left hc1 (sub_nonneg.mpr hd1)
    nlinarith

def evolve (a d : ℝ) : ℕ → (ℤ → ℝ) → (ℤ → ℝ)
  | 0,q => q
  | n+1,q => update a d (evolve a d n q)

theorem invariant_all_times (a d : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (q : ℤ → ℝ) (hq : ∀ i,0 ≤ q i ∧ q i ≤ 1) (n : ℕ) :
    ∀ i,0 ≤ evolve a d n q i ∧ evolve a d n q i ≤ 1 := by
  induction n with
  | zero => exact hq
  | succ n ih => exact invariant_step a d ha ha1 hd hd1 _ ih

theorem one_step_locality (a d : ℝ) (q p : ℤ → ℝ) (i : ℤ)
    (h0 : q i=p i) (hl : q (i-1)=p (i-1)) (hr : q (i+1)=p (i+1)) :
    update a d q i=update a d p i := by simp only [update,h0,hl,hr]

theorem finite_domain_of_dependence (a d : ℝ) (q p : ℤ → ℝ) (n : ℕ) (i : ℤ)
    (heq : ∀ j : ℤ, |j-i| ≤ (n:ℤ) → q j=p j) :
    evolve a d n q i=evolve a d n p i := by
  induction n generalizing i with
  | zero => exact heq i (by simp)
  | succ n ih =>
    apply one_step_locality
    · apply ih; intro j hj; apply heq; exact le_trans hj (by omega)
    · apply ih; intro j hj; apply heq
      have htri := abs_add_le (j-(i-1)) (-1:ℤ)
      have he : j-i=(j-(i-1))+(-1) := by ring
      rw [he]; norm_num at htri; omega
    · apply ih; intro j hj; apply heq
      have htri := abs_add_le (j-(i+1)) (1:ℤ)
      have he : j-i=(j-(i+1))+1 := by ring
      rw [he]; norm_num at htri; omega

theorem nonzero_depletion : update (1/2) (1/4) (fun _ => 1) 0=3/4 := by norm_num [update]

end Entropic.Completion.CausalBounds
