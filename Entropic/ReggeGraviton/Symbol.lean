import Entropic.ReggeGraviton.Data
import Entropic.ReggeGraviton.Taylor

/-!
# The gauge-reduced Regge kernel and its small-momentum limit

`KA c d q` is the metric–metric block `E(q)† M(q) E(q)` of the lattice Hessian (metric at edge
midpoints; short edges and body diagonals carry their metric values), `KB c j q` the coupling of
metric component `c` to the fluctuation of body diagonal `j`. The body-diagonal block is
`C(q) = −½ I` for every `q` (`MomentsB.bodyC_*`, `bodyD_*`), so integrating the body-diagonal
fluctuations out (Schur complement `A − B C⁻¹ B†`) gives

  `Kred q = KA q + 2 ∑_j KB_{·j}(q) KB_{·j}(q)†`.

The hyper-diagonal edge has an identically vanishing Hessian row and drops out. All entries are
finite trigonometric sums with integer coefficients.
-/

open Complex Filter Topology

namespace Entropic.ReggeGraviton

attribute [local irreducible] typ base hz simplexData hzL

abbrev Idx := Fin 24 × Fin 10 × Fin 10

/-- Half the pairing `q·D/2` of a momentum with a doubled lattice displacement. -/
noncomputable def dotH (q : Fin 4 → ℝ) (D : V4) : ℝ := (∑ i, q i * comp D i) / 2

noncomputable def phase (q : Fin 4 → ℝ) (D : V4) : ℂ := cexp ((dotH q D : ℂ) * I)

noncomputable def KA (c d : Fin 10) (q : Fin 4 → ℝ) : ℂ :=
  (1 / 48 : ℂ) * ∑ x : Idx, (cA c d x.1 x.2.1 x.2.2 : ℂ) * phase q (dA x.1 x.2.1 x.2.2)

noncomputable def KB (c : Fin 10) (j : Fin 4) (q : Fin 4 → ℝ) : ℂ :=
  (1 / 48 : ℂ) * ∑ x : Idx, (cB c j x.1 x.2.1 x.2.2 : ℂ) * phase q (dB x.1 x.2.1 x.2.2)

/-- The gauge-reduced quadratic Regge kernel on metric perturbations (per lattice cell). -/
noncomputable def Kred (q : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 10) ℂ :=
  fun c d => KA c d q + 2 * ∑ j, KB c j q * (starRingEnd ℂ) (KB d j q)

/-! ### Hermiticity -/

theorem dA_swap (p : Fin 24) (e f : Fin 10) : dA p f e = -dA p e f := by
  simp only [dA, DA]; abel

theorem cA_swap (c d : Fin 10) (p : Fin 24) (e f : Fin 10) : cA d c p f e = cA c d p e f := by
  simp only [cA, GA, hz_symm f e]; split_ifs <;> ring

theorem dotH_neg (q : Fin 4 → ℝ) (D : V4) : dotH q (-D) = -dotH q D := by
  simp only [dotH, comp, Prod.fst_neg, Prod.snd_neg]
  simp [Fin.sum_univ_four]; ring

theorem conj_phase (q : Fin 4 → ℝ) (D : V4) : (starRingEnd ℂ) (phase q D) = phase q (-D) := by
  rw [phase, phase, ← exp_conj, dotH_neg]
  simp [map_mul, conj_ofReal, conj_I]

theorem KA_herm (c d : Fin 10) (q : Fin 4 → ℝ) : KA d c q = (starRingEnd ℂ) (KA c d q) := by
  rw [KA, KA, map_mul, map_sum]
  congr 1
  · rw [map_div₀, map_one, map_ofNat]
  · let σ : Idx ≃ Idx :=
      { toFun := fun x => (x.1, x.2.2, x.2.1), invFun := fun x => (x.1, x.2.2, x.2.1),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [σ, Equiv.coe_fn_mk]
    rw [cA_swap, dA_swap, map_mul, map_intCast, conj_phase]

theorem Kred_herm (q : Fin 4 → ℝ) : (Kred q).IsHermitian := by
  ext c d
  rw [Matrix.conjTranspose_apply]
  change (starRingEnd ℂ) (Kred q d c) = Kred q c d
  simp only [Kred]
  rw [KA_herm d c q, map_add, map_mul, map_sum, map_ofNat]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

/-! ### Small-momentum limit -/

theorem fastSum_idx (G : V4 → V4 → V4 → V4 → ℤ → ℤ) : fastSum G = ∑ x : Idx,
    G (typ x.1 x.2.1) (base x.1 x.2.1) (typ x.1 x.2.2) (base x.1 x.2.2) (hz x.2.1 x.2.2) := by
  rw [fastSum_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_prod_type]

theorem dotH_smul (ε : ℝ) (k : Fin 4 → ℝ) (D : V4) : dotH (ε • k) D = ε * dotH k D := by
  simp only [dotH, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

theorem moment1_dotH (a : Idx → ℤ) (D : Idx → V4) (k : Fin 4 → ℝ) :
    ∑ x, (a x : ℝ) * dotH k (D x) = (∑ i, k i * ∑ x, ((a x * comp (D x) i : ℤ) : ℝ)) / 2 := by
  have h : ∀ x, (a x : ℝ) * dotH k (D x) = ∑ i, k i * ((a x * comp (D x) i : ℤ) : ℝ) / 2 := by
    intro x
    rw [dotH, mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]

theorem moment2_dotH (a : Idx → ℤ) (D : Idx → V4) (k : Fin 4 → ℝ) :
    ∑ x, (a x : ℝ) * dotH k (D x) ^ 2 =
      (∑ i, ∑ l, k i * k l * ∑ x, ((a x * comp (D x) i * comp (D x) l : ℤ) : ℝ)) / 4 := by
  have h : ∀ x, (a x : ℝ) * dotH k (D x) ^ 2 =
      ∑ i, ∑ l, k i * k l * ((a x * comp (D x) i * comp (D x) l : ℤ) : ℝ) / 4 := by
    intro x
    rw [dotH, div_pow, sq, Finset.sum_mul_sum, mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]

/-- Momentum moments as reals. -/
noncomputable def m2A (c d : Fin 10) (k : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ l, k i * k l * (momA2 c d i l : ℝ)
noncomputable def m1B (c : Fin 10) (j : Fin 4) (k : Fin 4 → ℝ) : ℝ := ∑ i, k i * (momB1 c j i : ℝ)

/-- The limit `ε⁻² Kred(εk)` predicted by the moments. -/
noncomputable def Lval (c d : Fin 10) (k : Fin 4 → ℝ) : ℂ :=
  ((-(1 / 384 : ℝ) * m2A c d k + (1 / 4608 : ℝ) * ∑ j, m1B c j k * m1B d j k : ℝ) : ℂ)

theorem KA_limit (c d : Fin 10) (k : Fin 4 → ℝ) (h0 : momA0 c d = 0)
    (h1 : ∀ i, momA1 c d i = 0) :
    Tendsto (fun ε : ℝ => KA c d (ε • k) / (ε : ℂ) ^ 2) (𝓝[≠] 0)
      (𝓝 ((-(1 / 384 : ℝ) * m2A c d k : ℝ) : ℂ)) := by
  set a : Idx → ℤ := fun x => cA c d x.1 x.2.1 x.2.2
  set θ : Idx → ℝ := fun x => dotH k (dA x.1 x.2.1 x.2.2)
  have hz0 : ∑ x, a x = 0 := by rw [← h0, momA0, fastSum_idx]; rfl
  have hz1 : ∑ x, (a x : ℝ) * θ x = 0 := by
    rw [moment1_dotH]
    have hi : ∀ i, ∑ x : Idx, a x * comp (dA x.1 x.2.1 x.2.2) i = 0 := fun i => by
      have := h1 i; rw [momA1, fastSum_idx] at this; exact this
    have : ∀ i, ∑ x : Idx, ((a x * comp (dA x.1 x.2.1 x.2.2) i : ℤ) : ℝ) = 0 := by
      intro i; rw [← Int.cast_sum, hi i, Int.cast_zero]
    rw [Finset.sum_eq_zero (fun i _ => by rw [this i, mul_zero]), zero_div]
  have hT := (tendsto_trig_second a θ hz0 hz1).const_mul (1 / 48 : ℂ)
  have e1 : ∀ ε : ℝ, KA c d (ε • k) / (ε : ℂ) ^ 2 =
      (1 / 48 : ℂ) * ((∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / (ε : ℂ) ^ 2) := by
    intro ε; simp only [KA, phase, dotH_smul, a, θ]; ring
  simp_rw [e1]
  convert hT using 2
  rw [Finset.mul_sum]
  have h2 := moment2_dotH a (fun x => dA x.1 x.2.1 x.2.2) k
  have hm : ∀ i l, ∑ x : Idx, ((a x * comp (dA x.1 x.2.1 x.2.2) i * comp (dA x.1 x.2.1 x.2.2) l : ℤ) : ℝ) =
      (momA2 c d i l : ℝ) := by
    intro i l; rw [momA2, fastSum_idx]; push_cast; rfl
  simp only [hm] at h2
  have : ∑ x, (1 / 48 : ℂ) * ((a x : ℂ) * (-(θ x : ℂ) ^ 2 / 2)) =
      (((-(1 / 96 : ℝ)) * ∑ x, (a x : ℝ) * θ x ^ 2 : ℝ) : ℂ) := by
    push_cast; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
  rw [this, h2, m2A]
  push_cast; ring

theorem KB_limit (c : Fin 10) (j : Fin 4) (k : Fin 4 → ℝ) (h0 : momB0 c j = 0) :
    Tendsto (fun ε : ℝ => KB c j (ε • k) / ε) (𝓝[≠] 0) (𝓝 (((1 / 96 : ℝ) * m1B c j k : ℝ) * I)) := by
  set a : Idx → ℤ := fun x => cB c j x.1 x.2.1 x.2.2
  set θ : Idx → ℝ := fun x => dotH k (dB x.1 x.2.1 x.2.2)
  have hz0 : ∑ x, a x = 0 := by rw [← h0, momB0, fastSum_idx]; rfl
  have hT := (tendsto_trig_first a θ hz0).const_mul (1 / 48 : ℂ)
  have e1 : ∀ ε : ℝ, KB c j (ε • k) / ε =
      (1 / 48 : ℂ) * ((∑ x, (a x : ℂ) * cexp ((ε * θ x : ℝ) * I)) / ε) := by
    intro ε; simp only [KB, phase, dotH_smul, a, θ]; ring
  simp_rw [e1]
  convert hT using 2
  have h1 := moment1_dotH a (fun x => dB x.1 x.2.1 x.2.2) k
  have hm : ∀ i, ∑ x : Idx, ((a x * comp (dB x.1 x.2.1 x.2.2) i : ℤ) : ℝ) = (momB1 c j i : ℝ) := by
    intro i; rw [momB1, fastSum_idx]; push_cast; rfl
  simp only [hm] at h1
  have : ∑ x, (1 / 48 : ℂ) * ((a x : ℂ) * ((θ x : ℂ) * I)) =
      ((((1 / 48 : ℝ)) * ∑ x, (a x : ℝ) * θ x : ℝ) : ℂ) * I := by
    push_cast; rw [Finset.mul_sum, Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.mul_sum, this]
  simp only [θ]
  rw [h1, m1B]
  push_cast; ring

/-- **Symbol limit.** Given the moment identities, `ε⁻² Kred(εk) → Lval k` entrywise. -/
theorem Kred_limit (c d : Fin 10) (k : Fin 4 → ℝ) (hA0 : momA0 c d = 0)
    (hA1 : ∀ i, momA1 c d i = 0) (hB0 : ∀ c' j, momB0 c' j = 0) :
    Tendsto (fun ε : ℝ => Kred (ε • k) c d / (ε : ℂ) ^ 2) (𝓝[≠] 0) (𝓝 (Lval c d k)) := by
  have hA := KA_limit c d k hA0 hA1
  have hB : ∀ j, Tendsto (fun ε : ℝ => KB c j (ε • k) / ε * (starRingEnd ℂ) (KB d j (ε • k) / ε))
      (𝓝[≠] 0) (𝓝 ((((1 / 96 : ℝ) * m1B c j k : ℝ) * I) *
        (starRingEnd ℂ) ((((1 / 96 : ℝ) * m1B d j k : ℝ) * I)))) :=
    fun j => (KB_limit c j k (hB0 c j)).mul ((continuous_conj.tendsto _).comp (KB_limit d j k (hB0 d j)))
  have hsum := (tendsto_finsetSum Finset.univ fun j _ => hB j).const_mul (2 : ℂ)
  have e : ∀ ε : ℝ, Kred (ε • k) c d / (ε : ℂ) ^ 2 = KA c d (ε • k) / (ε : ℂ) ^ 2 +
      2 * ∑ j, KB c j (ε • k) / ε * (starRingEnd ℂ) (KB d j (ε • k) / ε) := by
    intro ε
    simp only [Kred, map_div₀, conj_ofReal, add_div, Finset.mul_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  convert hA.add hsum using 2
  simp only [Lval, map_mul, conj_ofReal, conj_I]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf; rw [I_sq]; ring

end Entropic.ReggeGraviton
