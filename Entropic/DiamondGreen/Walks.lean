import Mathlib

/-!
# Diamond and fcc closed walks (C05-20, C05-21, C11-13)

The diamond lattice is two copies of the fcc Bravais lattice `ℤ³` (sublattices A and B,
in the primitive fcc basis). The A site at `n` is bonded to the B sites at `n + δᵢ`,
`δ = (0, e₁, e₂, e₃)`. Two diamond steps from an A site displace it by `δᵢ − δⱼ`: four
times by zero and once by each of the twelve fcc nearest-neighbour vectors. Hence, on
the A sublattice, (diamond adjacency)² = 4 · id + (fcc adjacency), and the number of
closed diamond walks of length `2n` is `∑ₖ C(n,k) 4^(n-k) · #(closed fcc walks of length k)`.

Walks are counted by the first-step recursion (transfer-matrix count): the number of walks
of length `L + 1` from `u` to `v` is the sum over the neighbours `w` of `u` of the number of
walks of length `L` from `w` to `v`.
-/

namespace Entropic.DiamondGreen

/-- The fcc Bravais lattice in its primitive basis. -/
abbrev Z3 := ℤ × ℤ × ℤ

/-- Diamond sites: `(false, n)` is the A site in cell `n`, `(true, n)` the B site. -/
abbrev DSite := Bool × Z3

/-- The four diamond bond offsets `δ = (0, e₁, e₂, e₃)`. -/
def bond : Fin 4 → Z3 := ![(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]

/-- The twelve fcc nearest-neighbour vectors `±e_i, ±(e_i − e_j)` in the primitive basis,
listed as the differences `δᵢ − δⱼ` with `i ≠ j`. -/
def fcc : Fin 12 → Z3 :=
  ![(-1, 0, 0), (0, -1, 0), (0, 0, -1),
    (1, 0, 0), (1, -1, 0), (1, 0, -1),
    (0, 1, 0), (-1, 1, 0), (0, 1, -1),
    (0, 0, 1), (-1, 0, 1), (0, -1, 1)]

/-- The four diamond neighbours of a site: A at `n` ↦ B at `n + δᵢ`, B at `m` ↦ A at `m − δᵢ`. -/
def dNbr : DSite → Fin 4 → DSite
  | (false, n), i => (true, n + bond i)
  | (true, m), i => (false, m - bond i)

/-- Number of diamond walks of length `L` from `u` to `v`. -/
def dWalks : ℕ → DSite → DSite → ℕ
  | 0, u, v => if u = v then 1 else 0
  | L + 1, u, v => ∑ i : Fin 4, dWalks L (dNbr u i) v

/-- Number of fcc walks of length `k` from `x` to `y`. -/
def fWalks : ℕ → Z3 → Z3 → ℕ
  | 0, x, y => if x = y then 1 else 0
  | k + 1, x, y => ∑ j : Fin 12, fWalks k (x + fcc j) y

/-! ### The lattice is the diamond lattice -/

/-- Adjacency is symmetric: B at `n + δᵢ` lists A at `n` among its neighbours. -/
theorem dNbr_symm (n : Z3) (i : Fin 4) : dNbr (dNbr (false, n) i) i = (false, n) := by
  simp [dNbr]

/-- Every site has four distinct neighbours (coordination number 4). -/
theorem dNbr_injective (u : DSite) : Function.Injective (dNbr u) := by
  obtain ⟨b, n⟩ := u
  intro i j h
  cases b <;> fin_cases i <;> fin_cases j <;> simp_all [dNbr, bond, Prod.ext_iff]

/-- The fcc neighbour set is symmetric under inversion and has twelve distinct vectors. -/
theorem fcc_injective : Function.Injective fcc := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [fcc]

theorem fcc_neg (j : Fin 12) : ∃ j', fcc j' = -fcc j := by
  fin_cases j
  · exact ⟨3, by simp [fcc]⟩
  · exact ⟨6, by simp [fcc]⟩
  · exact ⟨9, by simp [fcc]⟩
  · exact ⟨0, by simp [fcc]⟩
  · exact ⟨7, by simp [fcc]⟩
  · exact ⟨10, by simp [fcc]⟩
  · exact ⟨1, by simp [fcc]⟩
  · exact ⟨4, by simp [fcc]⟩
  · exact ⟨11, by simp [fcc]⟩
  · exact ⟨2, by simp [fcc]⟩
  · exact ⟨5, by simp [fcc]⟩
  · exact ⟨8, by simp [fcc]⟩

/-! ### Two diamond steps are `4 · id + (fcc step)` on the A sublattice -/

/-- Table of two-step displacements `δᵢ − δⱼ`. -/
def bondDiff : Fin 4 → Fin 4 → Z3 :=
  ![![0, fcc 0, fcc 1, fcc 2], ![fcc 3, 0, fcc 4, fcc 5],
    ![fcc 6, fcc 7, 0, fcc 8], ![fcc 9, fcc 10, fcc 11, 0]]

theorem bond_sub (i j : Fin 4) : bond i - bond j = bondDiff i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The sixteen two-step displacements `δᵢ − δⱼ`: zero four times, each fcc vector once. -/
theorem two_step_sum {M : Type*} [AddCommMonoid M] (F : Z3 → M) (y : Z3) :
    ∑ i : Fin 4, ∑ j : Fin 4, F (y + bond i - bond j) = 4 • F y + ∑ j : Fin 12, F (y + fcc j) := by
  simp only [add_sub_assoc, bond_sub]
  simp [Fin.sum_univ_succ, bondDiff]
  abel

theorem dWalks_two (L : ℕ) (y : Z3) (v : DSite) :
    dWalks (L + 2) (false, y) v = ∑ i : Fin 4, ∑ j : Fin 4, dWalks L (false, y + bond i - bond j) v := by
  simp [dWalks, dNbr]

/-! ### Operator form and the binomial expansion -/

/-- The fcc step operator `(T F)(y) = ∑ⱼ F(y + fccⱼ)`. -/
def T : Module.End ℕ (Z3 → ℕ) where
  toFun F y := ∑ j : Fin 12, F (y + fcc j)
  map_add' F G := by funext y; simp [Finset.sum_add_distrib]
  map_smul' c F := by funext y; simp [Finset.mul_sum]

/-- The point mass at `x`. -/
def delta (x : Z3) : Z3 → ℕ := fun y => if y = x then 1 else 0

theorem fWalks_eq_T_pow (k : ℕ) (x : Z3) : (fun y => fWalks k y x) = (T ^ k) (delta x) := by
  induction k with
  | zero => funext y; simp [fWalks, delta]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih]
    funext y; rfl

/-- The A→A two-step operator is `4 · id + T`. -/
theorem dWalks_even_eq (n : ℕ) (x : Z3) :
    (fun y => dWalks (2 * n) (false, y) (false, x)) = (((4 : Module.End ℕ (Z3 → ℕ)) + T) ^ n) (delta x) := by
  induction n with
  | zero => funext y; simp [dWalks, delta]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ← ih]
    funext y
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, dWalks_two, two_step_sum
      (fun z => dWalks (2 * n) (false, z) (false, x)) y]
    simp [T]

/-- **Diamond → fcc reduction.** For every `n` and every pair of A sites,
`#diamond walks of length 2n = ∑ₖ C(n,k) · 4^(n−k) · #fcc walks of length k`. -/
theorem dWalks_even (n : ℕ) (y x : Z3) :
    dWalks (2 * n) (false, y) (false, x) =
      ∑ k ∈ Finset.range (n + 1), n.choose k * 4 ^ (n - k) * fWalks k y x := by
  have h := congrFun (dWalks_even_eq n x) y
  rw [h, add_comm, (Commute.ofNat_right T 4).add_pow n, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h4 : ((4 : Module.End ℕ (Z3 → ℕ)) ^ (n - k)) = ((4 ^ (n - k) : ℕ) : Module.End ℕ (Z3 → ℕ)) := by
    push_cast; rfl
  rw [Module.End.mul_apply, Module.End.mul_apply, h4, Module.End.natCast_apply,
    Module.End.natCast_apply, map_nsmul, map_nsmul, ← fWalks_eq_T_pow]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Entropic.DiamondGreen
