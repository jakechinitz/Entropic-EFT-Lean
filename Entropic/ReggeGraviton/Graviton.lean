import Entropic.ReggeGraviton.Identify
import Entropic.ReggeGraviton.Resolvent

/-!
# The free graviton of the metric-Regge lattice (C08-61, C08-62)

At lattice spacing `a`, the gauge-reduced quadratic Regge operator acts on metric perturbations of
momentum `k ∈ BZ_a = [−π/a, π/a]⁴` by `Klat a k = a⁻² Kred(a k)`. The continuum operator is the
linearized Einstein–Hilbert kernel `KEH k`, the Fourier symbol of `(√g R)⁽²⁾`.

`regge_strong_resolvent`: for every `z` with `Im z ≠ 0` and every `f ∈ L²(ℝ⁴; ℂ¹⁰)`,
`‖1_{BZ_a} (Klat a − z)⁻¹ f − (KEH − z)⁻¹ f‖_{L²} → 0` as `a → 0⁺`. The lattice operators converge
to the linearized Einstein operator in the strong-resolvent sense.

This statement uses the plain inner product on the ten coordinates `h_c`. The physical
(Frobenius-normalized) version, in which transverse-traceless polarizations form an exact
eigenspace with eigenvalue `−¼|k|²`, is `Normalized.regge_strong_resolvent_normalized` and
`Normalized.KEHg_TT`.
-/

open Complex Filter Topology MeasureTheory Matrix

namespace Entropic.ReggeGraviton

attribute [local irreducible] typ base hz simplexData hzL

/-- The continuum kernel as a complex matrix. -/
noncomputable def KEHm (k : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 10) ℂ := fun c d => (KEH k c d : ℂ)

/-- The lattice kernel at spacing `a`, in physical momentum. -/
noncomputable def Klat (a : ℝ) (k : Fin 4 → ℝ) : Matrix (Fin 10) (Fin 10) ℂ :=
  fun c d => Kred (a • k) c d / (a : ℂ) ^ 2

/-- The rescaled Brillouin zone `[−π/a, π/a]⁴`. -/
def BZ (a : ℝ) : Set (Fin 4 → ℝ) := {k | ∀ i, |k i| ≤ Real.pi / a}

theorem KEHm_herm (k : Fin 4 → ℝ) : (KEHm k).IsHermitian := by
  ext c d
  simp [KEHm, Matrix.conjTranspose_apply, KEH_symm k d c]

theorem Klat_herm (a : ℝ) (k : Fin 4 → ℝ) : (Klat a k).IsHermitian := by
  ext c d
  rw [Matrix.conjTranspose_apply]
  change (starRingEnd ℂ) (Kred (a • k) d c / (a : ℂ) ^ 2) = Kred (a • k) c d / (a : ℂ) ^ 2
  rw [map_div₀, map_pow, conj_ofReal, ← (Kred_herm (a • k)).apply c d]
  rfl

theorem continuous_phase (D : V4) : Continuous fun q : Fin 4 → ℝ => phase q D := by
  unfold phase dotH; fun_prop

theorem continuous_KA (c d : Fin 10) : Continuous (KA c d) := by
  unfold KA
  exact continuous_const.mul (continuous_finsetSum _ fun x _ =>
    continuous_const.mul (continuous_phase _))

theorem continuous_KB (c : Fin 10) (j : Fin 4) : Continuous (KB c j) := by
  unfold KB
  exact continuous_const.mul (continuous_finsetSum _ fun x _ =>
    continuous_const.mul (continuous_phase _))

theorem continuous_Klat (a : ℝ) : Continuous (Klat a) := by
  refine continuous_pi fun c => continuous_pi fun d => ?_
  unfold Klat Kred
  have hs : Continuous fun k : Fin 4 → ℝ => a • k := by fun_prop
  refine Continuous.div_const ?_ _
  refine ((continuous_KA c d).comp hs).add (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_))
  exact ((continuous_KB c j).comp hs).mul (continuous_conj.comp ((continuous_KB d j).comp hs))

theorem continuous_KEHm : Continuous KEHm := by
  refine continuous_pi fun c => continuous_pi fun d => ?_
  unfold KEHm KEH
  fun_prop

theorem Klat_limit (k : Fin 4 → ℝ) : Tendsto (fun a => Klat a k) (𝓝[>] 0) (𝓝 (KEHm k)) := by
  refine tendsto_pi_nhds.mpr fun c => tendsto_pi_nhds.mpr fun d => ?_
  exact (symbol_limit k c d).mono_left (nhdsWithin_mono _ fun a (ha : 0 < a) => ha.ne')

theorem BZ_eventually (k : Fin 4 → ℝ) : ∀ᶠ a in 𝓝[>] (0 : ℝ), k ∈ BZ a := by
  set R : ℝ := ∑ i, |k i|
  have hR : ∀ i, |k i| ≤ R := fun i =>
    Finset.single_le_sum (f := fun i => |k i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have ht : Tendsto (fun a : ℝ => Real.pi / a) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop Real.pi_pos
    simpa [div_eq_mul_inv] using this
  filter_upwards [ht.eventually_ge_atTop R] with a ha i
  exact (hR i).trans ha

theorem measurableSet_BZ (a : ℝ) : MeasurableSet (BZ a) := by
  have : BZ a = ⋂ i, {k : Fin 4 → ℝ | |k i| ≤ Real.pi / a} := by ext; simp [BZ]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le ((measurable_pi_apply i).abs) measurable_const

/-- **Strong-resolvent convergence of the Regge graviton.** -/
theorem regge_strong_resolvent {z : ℂ} (hz : z.im ≠ 0) (f : (Fin 4 → ℝ) → Fin 10 → ℂ)
    (hfm : AEStronglyMeasurable f volume) (hfi : Integrable fun k => nrm2 (f k)) :
    Tendsto (fun a => ∫ k, nrm2 ((BZ a).indicator (fun k => (Klat a k - z • 1)⁻¹ *ᵥ f k) k -
      (KEHm k - z • 1)⁻¹ *ᵥ f k)) (𝓝[>] 0) (𝓝 0) :=
  strong_resolvent_conv Klat KEHm BZ BZ_eventually measurableSet_BZ Klat_herm KEHm_herm Klat_limit
    continuous_Klat continuous_KEHm hz f hfm hfi

end Entropic.ReggeGraviton
