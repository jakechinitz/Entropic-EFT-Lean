import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Finite reversible renewal (App. G.8, H.4, I.1, P.9).

What a finite reversible register can and cannot reproduce of exact memoryless renewal.
All window statements are counts over the uniform ensemble of register states.

* `kac_sum`: for any permutation of a finite set and any target set met by every orbit,
  the first-return times summed over the target equal the number of states (Kac's
  identity). No independence between ticks is assumed.
* The register `step τ` acts on `W = n + 1` cells with values in a finite set `M`: it
  shifts the cells by one and applies a fixed permutation `τ` to the cell that wraps
  around. It is a bijection (`stepEquiv`), and its reading at time `t` is
  `τ^(t / W)` applied to cell `t % W` (`pow_apply`).
* `window_count`: every window of `W` consecutive readings, starting at any time, takes
  each value in `M^W` exactly once over the ensemble. For a label map `ψ : M → L` the
  label window has the product law (`label_window_count`, `consecutive_pair_count`).
* `label_kac`: when `τ` is a single cycle, the mean first-return time of label `b` is
  `|M| / |ψ⁻¹ b|`, the reciprocal of its probability. Weighted by `p_b` it gives the
  number of labels with positive weight (`arithmetic_return_load`); its weighted
  logarithm gives the Shannon entropy (`geometric_return_load`).
* `reading_periodic`: the readings are periodic with period `W · orderOf τ`. Readings
  `W` ticks apart are deterministically related, the complete past fixes the present,
  and the entropy rate over unbounded windows is zero.

Reading for the manuscript. The arithmetic shell load `720^N` (I.1) holds exactly for
any finite reversible dynamics in which every orbit visits every shell state. Statistics
on windows of at most `W` ticks match exact renewal in the ensemble, for rational label
weights. Arguments that use unbounded windows do not transfer: the maximum-entropy-rate
selection of H.4, the almost-sure return asymptotics invoked in App. D, and the
transfer-operator gap of Section 13.3. A register has entropy rate zero, so the H.4
principle rejects it. -/

namespace Entropic.FiniteRenewal

open Finset

/-! ## Kac's identity for finite reversible dynamics -/

section Kac

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem exists_return (σ : Equiv.Perm Ω) (A : Finset Ω) (a : Ω) (ha : a ∈ A) :
    ∃ k, 0 < k ∧ (σ ^ k) a ∈ A :=
  ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; exact ha⟩

open Classical in
/-- First return time to `A` (zero off `A`). -/
noncomputable def returnTime (σ : Equiv.Perm Ω) (A : Finset Ω) (a : Ω) : ℕ :=
  if h : a ∈ A then Nat.find (exists_return σ A a h) else 0

open Classical in
theorem returnTime_spec (σ : Equiv.Perm Ω) (A : Finset Ω) {a : Ω} (ha : a ∈ A) :
    0 < returnTime σ A a ∧ (σ ^ returnTime σ A a) a ∈ A := by
  simp only [returnTime, ha, ↓reduceDIte]
  exact Nat.find_spec (exists_return σ A a ha)

open Classical in
theorem returnTime_min (σ : Equiv.Perm Ω) (A : Finset Ω) {a : Ω} (ha : a ∈ A) {k : ℕ}
    (hk0 : 0 < k) (hk : k < returnTime σ A a) : (σ ^ k) a ∉ A := by
  intro hmem
  simp only [returnTime, ha, ↓reduceDIte] at hk
  exact Nat.find_min (exists_return σ A a ha) hk ⟨hk0, hmem⟩

/-- Kac's identity: if every orbit meets `A`, the first-return times over `A` sum to the
number of states. -/
theorem kac_sum (σ : Equiv.Perm Ω) (A : Finset Ω)
    (hcov : ∀ ω : Ω, ∃ a ∈ A, ∃ j : ℕ, (σ ^ j) a = ω) :
    ∑ a ∈ A, returnTime σ A a = Fintype.card Ω := by
  classical
  have hsig : ∑ a ∈ A, returnTime σ A a
      = (A.sigma fun a => range (returnTime σ A a)).card := by
    rw [card_sigma]; simp
  rw [hsig, ← card_univ]
  -- injectivity helper: equal images force equal index pairs
  have key : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ j₁ j₂ : ℕ, j₂ < returnTime σ A a₂ → j₁ ≤ j₂ →
      (σ ^ j₁) a₁ = (σ ^ j₂) a₂ → j₁ = j₂ ∧ a₁ = a₂ := by
    intro a₁ h₁ a₂ h₂ j₁ j₂ hj₂ hle heq
    have hsplit : (σ ^ j₂) a₂ = (σ ^ j₁) ((σ ^ (j₂ - j₁)) a₂) := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
    rw [hsplit] at heq
    have ha : a₁ = (σ ^ (j₂ - j₁)) a₂ := (σ ^ j₁).injective heq
    by_cases hd : j₂ - j₁ = 0
    · refine ⟨by omega, ?_⟩
      rw [ha, hd, pow_zero]; rfl
    · exfalso
      exact returnTime_min σ A h₂ (Nat.pos_of_ne_zero hd) (by omega) (ha ▸ h₁)
  refine card_bij (fun x _ => (σ ^ x.2) x.1) (fun _ _ => mem_univ _) ?_ ?_
  · rintro ⟨a₁, j₁⟩ hx₁ ⟨a₂, j₂⟩ hx₂ heq
    simp only [mem_sigma, mem_range] at hx₁ hx₂
    simp only at heq
    rcases le_total j₁ j₂ with hle | hle
    · obtain ⟨rfl, rfl⟩ := key a₁ hx₁.1 a₂ hx₂.1 j₁ j₂ hx₂.2 hle heq; rfl
    · obtain ⟨rfl, rfl⟩ := key a₂ hx₂.1 a₁ hx₁.1 j₂ j₁ hx₁.2 hle heq.symm; rfl
  · intro ω _
    have hex : ∃ j, ∃ a ∈ A, (σ ^ j) a = ω := by
      obtain ⟨a, ha, j, hj⟩ := hcov ω; exact ⟨j, a, ha, hj⟩
    obtain ⟨a, ha, hj⟩ := Nat.find_spec hex
    refine ⟨⟨a, Nat.find hex⟩, ?_, hj⟩
    simp only [mem_sigma, mem_range]
    refine ⟨ha, ?_⟩
    by_contra hge
    push Not at hge
    obtain ⟨hpos, hmem⟩ := returnTime_spec σ A ha
    have h2 : (σ ^ (Nat.find hex - returnTime σ A a)) ((σ ^ returnTime σ A a) a) = ω := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hge, hj]
    have := Nat.find_min' hex ⟨_, hmem, h2⟩
    omega

end Kac

/-! ## The twisted shift register -/

section Register

variable {M : Type*} (n : ℕ) (τ : Equiv.Perm M)

/-- One tick: cell `i` takes the content of cell `i + 1`; the last cell takes `τ` of
cell `0`. -/
def step (ω : Fin (n + 1) → M) : Fin (n + 1) → M := fun i =>
  if h : i.val < n then ω ⟨i.val + 1, by omega⟩ else τ (ω 0)

/-- Inverse tick. -/
def unstep (ω : Fin (n + 1) → M) : Fin (n + 1) → M := fun i =>
  if h : 0 < i.val then ω ⟨i.val - 1, by omega⟩ else τ.symm (ω (Fin.last n))

theorem unstep_step (ω : Fin (n + 1) → M) : unstep n τ (step n τ ω) = ω := by
  funext i
  unfold unstep step
  by_cases h : 0 < i.val
  · have h' : i.val - 1 < n := by omega
    simp only [h, h', ↓reduceDIte]
    congr 1; ext; simp; omega
  · have h' : ¬ (Fin.last n).val < n := by simp
    simp only [h, h', ↓reduceDIte, Equiv.symm_apply_apply]
    congr 1; ext; simp; omega

theorem step_unstep (ω : Fin (n + 1) → M) : step n τ (unstep n τ ω) = ω := by
  funext i
  unfold unstep step
  by_cases h : i.val < n
  · have h' : 0 < i.val + 1 := by omega
    simp only [h, h', ↓reduceDIte]
    all_goals (congr 1)
  · have h' : ¬ 0 < (0 : Fin (n + 1)).val := by simp
    simp only [h, h', ↓reduceDIte, Equiv.apply_symm_apply]
    congr 1; ext; simp; omega

/-- The register tick as a permutation of the state space. -/
def stepEquiv : Equiv.Perm (Fin (n + 1) → M) where
  toFun := step n τ
  invFun := unstep n τ
  left_inv := unstep_step n τ
  right_inv := step_unstep n τ

/-- Reading of the register at absolute position `t`. -/
def read (ω : Fin (n + 1) → M) (t : ℕ) : M :=
  (τ ^ (t / (n + 1))) (ω ⟨t % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩)

theorem read_of_lt (ω : Fin (n + 1) → M) (i : Fin (n + 1)) : read n τ ω i.val = ω i := by
  unfold read
  rw [Nat.div_eq_of_lt i.isLt, pow_zero]
  simp only [Equiv.Perm.coe_one, id_eq]
  congr 1; ext; simp [Nat.mod_eq_of_lt i.isLt]

theorem read_add_period (ω : Fin (n + 1) → M) (t : ℕ) :
    read n τ ω (t + (n + 1)) = τ (read n τ ω t) := by
  unfold read
  have e1 : (t + (n + 1)) / (n + 1) = t / (n + 1) + 1 := Nat.add_div_right t (Nat.succ_pos n)
  have e2 : (t + (n + 1)) % (n + 1) = t % (n + 1) := Nat.add_mod_right t (n + 1)
  simp only [e1, e2, pow_succ', Equiv.Perm.mul_apply]

/-- Cell `i` after `t` ticks holds the reading at position `t + i`. -/
theorem pow_apply (ω : Fin (n + 1) → M) (t : ℕ) (i : Fin (n + 1)) :
    ((stepEquiv n τ) ^ t) ω i = read n τ ω (t + i.val) := by
  induction t generalizing i with
  | zero => simpa using (read_of_lt n τ ω i).symm
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    show step n τ (((stepEquiv n τ) ^ t) ω) i = _
    unfold step
    by_cases h : i.val < n
    · simp only [h, ↓reduceDIte]; rw [ih]; congr 1; simp; omega
    · simp only [h, ↓reduceDIte]; rw [ih]
      have hi : i.val = n := by omega
      rw [hi, show t + 1 + n = t + (n + 1) by omega, read_add_period]
      simp

/-- The reading process: label of the state after `t` ticks. -/
def reading (ω : Fin (n + 1) → M) (t : ℕ) : M := ((stepEquiv n τ) ^ t) ω 0

theorem reading_eq (ω : Fin (n + 1) → M) (t : ℕ) : reading n τ ω t = read n τ ω t := by
  simp [reading, pow_apply]

theorem pow_period (ω : Fin (n + 1) → M) (k : ℕ) :
    ((stepEquiv n τ) ^ ((n + 1) * k)) ω = fun i => (τ ^ k) (ω i) := by
  funext i
  rw [pow_apply]
  unfold read
  have e1 : ((n + 1) * k + i.val) / (n + 1) = k := by
    rw [Nat.mul_add_div (Nat.succ_pos n), Nat.div_eq_of_lt i.isLt, add_zero]
  have e2 : ((n + 1) * k + i.val) % (n + 1) = i.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [e1, e2]

/-- The reading process is periodic with period `(n + 1) · orderOf τ`. -/
theorem reading_periodic [Finite M] (ω : Fin (n + 1) → M) (t : ℕ) :
    reading n τ ω (t + (n + 1) * orderOf τ) = reading n τ ω t := by
  rw [reading, pow_add, Equiv.Perm.mul_apply, pow_period, pow_orderOf_eq_one]
  rfl

variable [Fintype M] [DecidableEq M]

/-- Every window of `n + 1` consecutive readings, from any start, takes each value
exactly once over the state space. -/
theorem window_count (t₀ : ℕ) (v : Fin (n + 1) → M) :
    (univ.filter fun ω : Fin (n + 1) → M =>
      ∀ i : Fin (n + 1), reading n τ ω (t₀ + i.val) = v i).card = 1 := by
  rw [card_eq_one]
  refine ⟨(((stepEquiv n τ) ^ t₀).symm) v, ?_⟩
  ext ω
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  have hr : ∀ i : Fin (n + 1), reading n τ ω (t₀ + i.val) = ((stepEquiv n τ) ^ t₀) ω i := by
    intro i
    rw [reading_eq, pow_apply]
  simp only [hr]
  constructor
  · intro h
    rw [Equiv.eq_symm_apply]; funext i; exact h i
  · intro h i
    rw [h, Equiv.apply_symm_apply]

omit [DecidableEq M] in
/-- Label windows have the product law: the number of states whose labels at times
`t₀, …, t₀ + n` equal `ℓ` is the product of the label fibre sizes. -/
theorem label_window_count {L : Type*} [DecidableEq L] (ψ : M → L) (t₀ : ℕ)
    (ℓ : Fin (n + 1) → L) :
    (univ.filter fun ω : Fin (n + 1) → M =>
      ∀ i : Fin (n + 1), ψ (reading n τ ω (t₀ + i.val)) = ℓ i).card
      = ∏ i, (univ.filter fun x : M => ψ x = ℓ i).card := by
  rw [← Fintype.card_piFinset]
  refine card_bij (fun ω _ => ((stepEquiv n τ) ^ t₀) ω) ?_ ?_ ?_
  · intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
    intro i; rw [← hω i, reading_eq, pow_apply]
  · intro a _ b _ h; exact ((stepEquiv n τ) ^ t₀).injective h
  · intro v hv
    simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and] at hv
    refine ⟨(((stepEquiv n τ) ^ t₀).symm) v, ?_, Equiv.apply_symm_apply _ _⟩
    simp only [mem_filter, mem_univ, true_and]
    intro i
    rw [reading_eq, ← pow_apply, Equiv.apply_symm_apply, hv i]

omit [DecidableEq M] in
/-- Two consecutive readings are independent: the number of states with labels `a`
then `b` at times `t₀, t₀ + 1` is `|ψ⁻¹ a| · |ψ⁻¹ b| · |M|^m` out of `|M|^(m+2)`, the
product of the one-time marginals (register length `m + 2 ≥ 2`). -/
theorem consecutive_pair_count {L : Type*} [DecidableEq L] (m : ℕ) (σ' : Equiv.Perm M)
    (ψ : M → L) (t₀ : ℕ) (a b : L) :
    (univ.filter fun ω : Fin (m + 2) → M =>
      ψ (reading (m + 1) σ' ω t₀) = a ∧ ψ (reading (m + 1) σ' ω (t₀ + 1)) = b).card
      = (univ.filter fun x : M => ψ x = a).card * (univ.filter fun x : M => ψ x = b).card
        * Fintype.card M ^ m := by
  classical
  have e : (univ.filter fun ω : Fin (m + 2) → M =>
      ψ (reading (m + 1) σ' ω t₀) = a ∧ ψ (reading (m + 1) σ' ω (t₀ + 1)) = b).card
      = (Fintype.piFinset fun i : Fin (m + 2) =>
          if i.val = 0 then univ.filter (fun x : M => ψ x = a)
          else if i.val = 1 then univ.filter (fun x : M => ψ x = b) else univ).card := by
    refine card_bij (fun ω _ => ((stepEquiv (m + 1) σ') ^ t₀) ω) ?_ ?_ ?_
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp only [Fintype.mem_piFinset]
      intro i
      by_cases h0 : i.val = 0
      · simp only [h0, ↓reduceIte]; simp only [mem_filter, mem_univ, true_and]
        rw [pow_apply, h0, add_zero, ← reading_eq]; exact hω.1
      · simp only [h0, ↓reduceIte]
        by_cases h1 : i.val = 1
        · simp only [h1, ↓reduceIte]; simp only [mem_filter, mem_univ, true_and]
          rw [pow_apply, h1, ← reading_eq]; exact hω.2
        · simp only [h1, ↓reduceIte]; exact mem_univ _
    · intro x _ y _ h; exact ((stepEquiv (m + 1) σ') ^ t₀).injective h
    · intro v hv
      simp only [Fintype.mem_piFinset] at hv
      refine ⟨(((stepEquiv (m + 1) σ') ^ t₀).symm) v, ?_, Equiv.apply_symm_apply _ _⟩
      simp only [mem_filter, mem_univ, true_and]
      have h0 := hv 0
      have h1 := hv 1
      have v0 : ((1 : Fin (m + 2)).val) = 1 := by simp
      simp only [Fin.val_zero, ↓reduceIte] at h0
      simp only [v0, one_ne_zero, ↓reduceIte] at h1
      simp only [mem_filter, mem_univ, true_and] at h0 h1
      constructor
      · have := pow_apply (m + 1) σ' ((((stepEquiv (m + 1) σ') ^ t₀).symm) v) t₀ 0
        rw [Equiv.apply_symm_apply] at this
        rw [reading_eq]; simp only [Fin.val_zero, add_zero] at this; rw [← this]; exact h0
      · have := pow_apply (m + 1) σ' ((((stepEquiv (m + 1) σ') ^ t₀).symm) v) t₀ 1
        rw [Equiv.apply_symm_apply, v0] at this
        rw [reading_eq, ← this]; exact h1
  rw [e, Fintype.card_piFinset, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have hrest : ∀ j : Fin m, ((Fin.succ (Fin.succ j)) : Fin (m + 2)).val ≠ 0 ∧
      ((Fin.succ (Fin.succ j)) : Fin (m + 2)).val ≠ 1 := by
    intro j; simp
  have h1 : ((Fin.succ (0 : Fin (m + 1))) : Fin (m + 2)).val = 1 := by simp
  simp only [Fin.val_zero, h1, one_ne_zero, ↓reduceIte]
  simp only [(hrest _).1, (hrest _).2, ↓reduceIte, card_univ, prod_const, Fintype.card_fin]
  ring

end Register

/-! ## Return times of labels -/

section LabelKac

variable {M : Type*} [Fintype M] [DecidableEq M] (n : ℕ) (τ : Equiv.Perm M)
variable {L : Type*} [DecidableEq L] (ψ : M → L)

/-- States whose current reading has label `b`. -/
def labelSet (b : L) : Finset (Fin (n + 1) → M) := univ.filter fun ω => ψ (ω 0) = b

/-- Fibre of the label map. -/
def fibre (b : L) : Finset M := univ.filter fun x => ψ x = b

omit [DecidableEq M] in
theorem mem_labelSet (b : L) (ω : Fin (n + 1) → M) :
    ω ∈ labelSet n ψ b ↔ reading n τ ω 0 = ω 0 ∧ ψ (ω 0) = b := by
  simp [labelSet, reading]

omit [DecidableEq M] in
/-- If `τ` is a single cycle, every orbit of the register meets every nonempty label. -/
theorem label_cover (hτ : ∀ x z : M, ∃ k : ℕ, (τ ^ k) z = x) (b : L) (hb : ∃ z, ψ z = b) :
    ∀ ω, ∃ a ∈ labelSet n ψ b, ∃ j : ℕ, ((stepEquiv n τ) ^ j) a = ω := by
  intro ω
  obtain ⟨z, hz⟩ := hb
  obtain ⟨k, hk⟩ := hτ (ω 0) z
  refine ⟨fun i => ((τ ^ k).symm) (ω i), ?_, (n + 1) * k, ?_⟩
  · simp only [labelSet, mem_filter, mem_univ, true_and]
    rw [← hk, Equiv.symm_apply_apply, hz]
  · rw [pow_period]; funext i; simp

omit [DecidableEq M] in
theorem labelSet_card (b : L) :
    (labelSet n ψ b).card = (fibre ψ b).card * Fintype.card M ^ n := by
  classical
  have e : labelSet n ψ b = Fintype.piFinset fun i : Fin (n + 1) =>
      if i = 0 then fibre ψ b else univ := by
    ext ω
    simp only [labelSet, fibre, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i = 0
      · subst hi; simpa using h
      · simp [hi]
    · intro h; simpa using h 0
  rw [e, Fintype.card_piFinset, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero, prod_const]

/-- Kac's identity for a label: the first-return times summed over the states carrying
label `b` equal the number of register states, `|M|^(n+1)`. -/
theorem label_kac (hτ : ∀ x z : M, ∃ k : ℕ, (τ ^ k) z = x) (b : L) (hb : ∃ z, ψ z = b) :
    ∑ ω ∈ labelSet n ψ b, returnTime (stepEquiv n τ) (labelSet n ψ b) ω
      = Fintype.card M ^ (n + 1) := by
  rw [kac_sum _ _ (label_cover n τ ψ hτ b hb)]
  simp

/-- Mean first-return time of label `b` over the uniform ensemble of its states. -/
noncomputable def meanReturn (b : L) : ℝ :=
  (∑ ω ∈ labelSet n ψ b, (returnTime (stepEquiv n τ) (labelSet n ψ b) ω : ℝ))
    / ((labelSet n ψ b).card : ℝ)

/-- One-time probability of label `b`. -/
noncomputable def prob (b : L) : ℝ := ((fibre ψ b).card : ℝ) / (Fintype.card M : ℝ)

/-- The mean return time is the reciprocal probability: `|M| / |ψ⁻¹ b|`. -/
theorem meanReturn_eq (hτ : ∀ x z : M, ∃ k : ℕ, (τ ^ k) z = x) (b : L)
    (hb : ∃ z, ψ z = b) :
    meanReturn n τ ψ b = (Fintype.card M : ℝ) / ((fibre ψ b).card : ℝ) := by
  have hsum := label_kac n τ ψ hτ b hb
  have hcard := labelSet_card n ψ b
  obtain ⟨z, hz⟩ := hb
  have hF : 0 < (fibre ψ b).card := card_pos.mpr ⟨z, by simp [fibre, hz]⟩
  have hM : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨z⟩
  unfold meanReturn
  rw [← Nat.cast_sum, hsum, hcard]
  have hF' : (0 : ℝ) < (fibre ψ b).card := by exact_mod_cast hF
  have hM' : (0 : ℝ) < Fintype.card M := by exact_mod_cast hM
  push_cast
  field_simp
  ring

theorem prob_mul_meanReturn (hτ : ∀ x z : M, ∃ k : ℕ, (τ ^ k) z = x) (b : L)
    (hb : ∃ z, ψ z = b) : prob ψ b * meanReturn n τ ψ b = 1 := by
  rw [meanReturn_eq n τ ψ hτ b hb, prob]
  obtain ⟨z, hz⟩ := hb
  have hF : (0 : ℝ) < (fibre ψ b).card := by
    exact_mod_cast card_pos.mpr ⟨z, by simp [fibre, hz]⟩
  have hM : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨z⟩
  field_simp

omit [DecidableEq M] in
theorem prob_eq_zero (b : L) (hb : ¬ ∃ z, ψ z = b) : prob ψ b = 0 := by
  have : fibre ψ b = ∅ := by
    ext x; simp only [fibre, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun h => hb ⟨x, h⟩
  simp [prob, this]

/-- Arithmetic recurrence load: the probability-weighted mean return time equals the
number of labels of positive probability. For the shell register this is `720` per
shell, with no assumption of independence between ticks. -/
theorem arithmetic_return_load [Fintype L] (hτ : ∀ x z : M, ∃ k : ℕ, (τ ^ k) z = x) :
    ∑ b, prob ψ b * meanReturn n τ ψ b
      = ((univ.filter fun b : L => ∃ z, ψ z = b).card : ℝ) := by
  classical
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : ∃ z, ψ z = b
  · simp only [hb, ↓reduceIte, prob_mul_meanReturn n τ ψ hτ b hb, Nat.cast_one]
  · simp only [hb, ↓reduceIte, prob_eq_zero ψ b hb, zero_mul]

/-- Geometric recurrence load: the probability-weighted logarithm of the mean return
time equals the Shannon entropy of the label distribution. -/
theorem geometric_return_load [Fintype L] (hτ : ∀ x z : M, ∃ k : ℕ, (τ ^ k) z = x) :
    ∑ b, prob ψ b * Real.log (meanReturn n τ ψ b)
      = -∑ b, prob ψ b * Real.log (prob ψ b) := by
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun b _ => ?_
  by_cases hb : ∃ z, ψ z = b
  · have h1 := prob_mul_meanReturn n τ ψ hτ b hb
    have hp : prob ψ b ≠ 0 := by intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
    have hm : meanReturn n τ ψ b = (prob ψ b)⁻¹ := by
      field_simp; linarith [h1]
    rw [hm, Real.log_inv]; ring
  · simp [prob_eq_zero ψ b hb]

end LabelKac

/-! ## A single cycle exists on every nonempty finite set -/

open Fin.NatCast in
theorem finRotate_pow_apply (N : ℕ) (k : ℕ) (z : Fin (N + 1)) :
    ((finRotate (N + 1)) ^ k) z = z + (k : Fin (N + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, finRotate_apply, Nat.cast_succ, add_assoc]

open Fin.NatCast in
theorem finRotate_transitive (N : ℕ) (x z : Fin (N + 1)) :
    ∃ k : ℕ, ((finRotate (N + 1)) ^ k) z = x :=
  ⟨(x - z).val, by rw [finRotate_pow_apply, Fin.cast_val_eq_self, add_sub_cancel]⟩

/-! ## Summary for the coefficient chains -/

/-- A finite reversible register with `n + 2 ≥ 2` cells over `Fin (N + 1)` and the single
cycle `finRotate` has, for every label map: independent consecutive readings with the
product law; exact Kac return times `1 / p_b`; and periodic readings. -/
theorem finite_register_reproduces {L : Type*} [Fintype L] [DecidableEq L] (N m : ℕ)
    (ψ : Fin (N + 1) → L) :
    (∀ t₀ (a b : L),
      (univ.filter fun ω : Fin (m + 2) → Fin (N + 1) =>
        ψ (reading (m + 1) (finRotate (N + 1)) ω t₀) = a ∧
        ψ (reading (m + 1) (finRotate (N + 1)) ω (t₀ + 1)) = b).card
        = (fibre ψ a).card * (fibre ψ b).card * (N + 1) ^ m) ∧
    (∑ b, prob ψ b * meanReturn (m + 1) (finRotate (N + 1)) ψ b
      = ((univ.filter fun b : L => ∃ z, ψ z = b).card : ℝ)) ∧
    (∑ b, prob ψ b * Real.log (meanReturn (m + 1) (finRotate (N + 1)) ψ b)
      = -∑ b, prob ψ b * Real.log (prob ψ b)) ∧
    (∀ ω t, reading (m + 1) (finRotate (N + 1)) ω (t + (m + 2) * orderOf (finRotate (N + 1)))
      = reading (m + 1) (finRotate (N + 1)) ω t) := by
  refine ⟨fun t₀ a b => ?_, by convert arithmetic_return_load (m + 1) _ ψ (finRotate_transitive N),
    geometric_return_load (m + 1) _ ψ (finRotate_transitive N),
    fun ω t => reading_periodic (m + 1) _ ω t⟩
  rw [consecutive_pair_count]; simp [fibre]


end Entropic.FiniteRenewal
