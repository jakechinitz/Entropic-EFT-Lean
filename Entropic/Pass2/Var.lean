import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic

/-! Second pass, chunk 16: first variation on ℝⁿ.

For a C¹ Lagrangian density L(x, u, p) (x ∈ ℝⁿ, u ∈ ℝ, p ∈ ℝⁿ), a C¹ field u and a C¹ compactly supported
variation η, the action difference ε ↦ ∫ [L(x, u + εη, ∇u + ε∇η) − L(x, u, ∇u)] dx is differentiable at
ε = 0 with derivative ∫ (L_u η + L_p · ∇η) (`gateaux`). Integration by parts (`ibp`, `ibp_div`) and the
fundamental lemma of the calculus of variations (`fund`) turn stationarity under all test variations into
the pointwise Euler–Lagrange equation L_u = div L_p (`euler_lagrange`). Differences of actions are used so
that no integrability of L itself is needed. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Entropic.Var

variable {n : ℕ}

/-- ℝⁿ. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Coordinate unit vector. -/
noncomputable def ev (i : Fin n) : E n := EuclideanSpace.single i 1

/-- Partial derivative ∂ᵢ f. -/
noncomputable def pd (f : E n → ℝ) (i : Fin n) (x : E n) : ℝ := fderiv ℝ f x (ev i)

/-- Gradient in coordinates. -/
noncomputable def grad (f : E n → ℝ) (x : E n) : Fin n → ℝ := fun i => pd f i x

/-- Divergence of a vector field given by its components. -/
noncomputable def dvg (V : Fin n → E n → ℝ) (x : E n) : ℝ := ∑ i, pd (V i) i x

/-- Laplacian Δf = div ∇f. -/
noncomputable def lap (f : E n → ℝ) : E n → ℝ := dvg (fun i => pd f i)

/-- Test functions: smooth and compactly supported. -/
def IsTest (η : E n → ℝ) : Prop := ContDiff ℝ ∞ η ∧ HasCompactSupport η

theorem IsTest.c1 {η : E n → ℝ} (h : IsTest η) : ContDiff ℝ 1 η := h.1.of_le (by exact_mod_cast le_top)

theorem pd_continuous {f : E n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) : Continuous (pd f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem grad_continuous {f : E n → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (grad f) :=
  continuous_pi fun i => pd_continuous hf i

theorem pd_contDiff {f : E n → ℝ} {m : ℕ} (hf : ContDiff ℝ (m + 1) f) (i : Fin n) : ContDiff ℝ m (pd f i) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem pd_eq_zero {f : E n → ℝ} {x : E n} (hx : x ∉ tsupport f) (i : Fin n) : pd f i x = 0 := by
  simp [pd, fderiv_of_notMem_tsupport ℝ hx]

theorem pd_hasCompactSupport {f : E n → ℝ} (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (pd f i) :=
  hf.fderiv_apply (𝕜 := ℝ) (ev i)

theorem integrable_of_cs {f : E n → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) : Integrable f :=
  hf.integrable_of_hasCompactSupport hc

/-- Integration by parts against a C¹ compactly supported function. -/
theorem ibp {η g : E n → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (hg : ContDiff ℝ 1 g)
    (i : Fin n) : ∫ x, η x * pd g i x = -∫ x, pd η i x * g x := by
  have hηd : Differentiable ℝ η := hη.differentiable one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := ev i)
    (integrable_of_cs ((pd_continuous hη i).mul hg.continuous) ((pd_hasCompactSupport hηc i).mul_right))
    (integrable_of_cs (hη.continuous.mul (pd_continuous hg i)) hηc.mul_right)
    (integrable_of_cs (hη.continuous.mul hg.continuous) hηc.mul_right)
    (fun x _ => hηd x) (fun x _ => hgd x)

/-- ∫ η div V = −∫ ∇η · V. -/
theorem ibp_div {η : E n → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) {V : Fin n → E n → ℝ}
    (hV : ∀ i, ContDiff ℝ 1 (V i)) : ∫ x, η x * dvg V x = -∫ x, ∑ i, pd η i x * V i x := by
  simp only [dvg, Finset.mul_sum]
  rw [integral_finsetSum (f := fun i x => η x * pd (V i) i x) _
      (fun i _ => integrable_of_cs (hη.continuous.mul (pd_continuous (hV i) i)) hηc.mul_right),
    integral_finsetSum (f := fun i x => pd η i x * V i x) _
      (fun i _ => integrable_of_cs ((pd_continuous hη i).mul (hV i).continuous)
        (pd_hasCompactSupport hηc i).mul_right), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => ibp hη hηc (hV i) i)

/-- Fundamental lemma of the calculus of variations (continuous version). -/
theorem fund {g : E n → ℝ} (hg : Continuous g) (h : ∀ η, IsTest η → ∫ x, η x * g x = 0) : g = 0 := by
  have hae : ∀ᵐ x ∂(volume : Measure (E n)), g x = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hg.locallyIntegrable
      (fun η hη hc => by simpa [smul_eq_mul] using h η ⟨hη, hc⟩)
  exact (Continuous.ae_eq_iff_eq volume hg continuous_const).1 hae

/-- A Lagrangian density with continuous line derivatives in (u, p). -/
structure Lag (n : ℕ) where
  L : E n → ℝ → (Fin n → ℝ) → ℝ
  Lu : E n → ℝ → (Fin n → ℝ) → ℝ
  Lp : Fin n → E n → ℝ → (Fin n → ℝ) → ℝ
  line : ∀ x u p a (b : Fin n → ℝ),
    HasDerivAt (fun ε : ℝ => L x (u + ε * a) (p + ε • b)) (Lu x u p * a + ∑ i, Lp i x u p * b i) 0
  cont : Continuous fun z : E n × ℝ × (Fin n → ℝ) => L z.1 z.2.1 z.2.2
  cont_u : Continuous fun z : E n × ℝ × (Fin n → ℝ) => Lu z.1 z.2.1 z.2.2
  cont_p : ∀ i, Continuous fun z : E n × ℝ × (Fin n → ℝ) => Lp i z.1 z.2.1 z.2.2

/-- Action difference A(u + εη) − A(u). -/
noncomputable def dA (Λ : Lag n) (u η : E n → ℝ) (ε : ℝ) : ℝ :=
  ∫ x, (Λ.L x (u x + ε * η x) (grad u x + ε • grad η x) - Λ.L x (u x) (grad u x))

/-- First variation ∫ (L_u η + L_p · ∇η). -/
noncomputable def δA (Λ : Lag n) (u η : E n → ℝ) : ℝ :=
  ∫ x, (Λ.Lu x (u x) (grad u x) * η x + ∑ i, Λ.Lp i x (u x) (grad u x) * pd η i x)

/-- The first-variation formula: d/dε [A(u + εη) − A(u)] at ε = 0 equals δA. -/
theorem gateaux (Λ : Lag n) {u η : E n → ℝ} (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) : HasDerivAt (dA Λ u η) (δA Λ u η) 0 := by
  set F : ℝ → E n → ℝ := fun ε x =>
    Λ.L x (u x + ε * η x) (grad u x + ε • grad η x) - Λ.L x (u x) (grad u x) with hF
  set F' : ℝ → E n → ℝ := fun ε x =>
    Λ.Lu x (u x + ε * η x) (grad u x + ε • grad η x) * η x +
      ∑ i, Λ.Lp i x (u x + ε * η x) (grad u x + ε • grad η x) * pd η i x with hF'
  have hgu := grad_continuous hu
  have hgη := grad_continuous hη
  have hG : Continuous fun q : ℝ × E n => (q.2, u q.2 + q.1 * η q.2, grad u q.2 + q.1 • grad η q.2) := by
    fun_prop
  have hF'c : Continuous fun q : ℝ × E n => F' q.1 q.2 := by
    simp only [hF']
    refine (Λ.cont_u.comp hG).mul (hη.continuous.comp continuous_snd) |>.add ?_
    exact continuous_finsetSum _ fun i _ => ((Λ.cont_p i).comp hG).mul ((pd_continuous hη i).comp continuous_snd)
  have hFc : ∀ ε, Continuous (F ε) := fun ε => by
    simp only [hF]
    refine ((Λ.cont.comp ((hG.comp (Continuous.prodMk continuous_const continuous_id)))).sub ?_)
    exact Λ.cont.comp (continuous_id.prodMk (hu.continuous.prodMk hgu))
  set K := tsupport η
  have hK : IsCompact K := hηc
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℝ) 1).prod hK |>.exists_bound_of_continuousOn hF'c.continuousOn
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0:ℝ))
    (s := Metric.ball 0 1) (bound := K.indicator fun _ => C) (F := F) (F' := F') (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun ε => (hFc ε).aestronglyMeasurable)
    (by
      have : F 0 = 0 := by funext x; simp [hF]
      rw [this]; exact integrable_zero _ _ _)
    (hF'c.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun x ε hε => by
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        exact hC (ε, x) ⟨Metric.ball_subset_closedBall hε, hx⟩
      · rw [Set.indicator_of_notMem hx]
        have h0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hF', h0, pd_eq_zero hx])
    ((integrable_indicator_iff (isClosed_tsupport η).measurableSet).2
      (integrableOn_const (hK.measure_lt_top.ne)))
    (Eventually.of_forall fun x ε _ => by
      have h := Λ.line x (u x + ε * η x) (grad u x + ε • grad η x) (η x) (grad η x)
      have h2 := HasDerivAt.comp_sub_const ε ε (by rw [sub_self]; exact h)
      refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)).sub_const _
      simp only [grad]
      congr 1
      · ring
      · funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
  have h2 := hmain.2
  have e1 : (fun ε => ∫ x, F ε x) = dA Λ u η := rfl
  have e2 : ∫ x, F' 0 x = δA Λ u η := by
    simp only [hF', δA, zero_mul, add_zero, zero_smul, grad]
  rw [e1, e2] at h2; exact h2

/-- After integration by parts, δA = ∫ η (L_u − div L_p). -/
theorem first_variation_ibp (Λ : Lag n) {u η : E n → ℝ} (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hV : ∀ i, ContDiff ℝ 1 fun y => Λ.Lp i y (u y) (grad u y)) :
    δA Λ u η = ∫ x, η x * (Λ.Lu x (u x) (grad u x) - dvg (fun i y => Λ.Lp i y (u y) (grad u y)) x) := by
  have hgu := grad_continuous hu
  have hLu : Continuous fun y => Λ.Lu y (u y) (grad u y) :=
    Λ.cont_u.comp (continuous_id.prodMk (hu.continuous.prodMk hgu))
  have h1 : Integrable fun x => Λ.Lu x (u x) (grad u x) * η x :=
    integrable_of_cs (hLu.mul hη.continuous) hηc.mul_left
  have h2 : Integrable fun x => ∑ i, Λ.Lp i x (u x) (grad u x) * pd η i x :=
    integrable_of_cs (continuous_finsetSum _ fun i _ => (hV i).continuous.mul (pd_continuous hη i))
      (by
        refine HasCompactSupport.intro hηc.isCompact fun x hx => ?_
        simp [pd_eq_zero hx])
  have h3 : Integrable fun x => η x * Λ.Lu x (u x) (grad u x) :=
    integrable_of_cs (hη.continuous.mul hLu) hηc.mul_right
  have h4 : Integrable fun x => η x * dvg (fun i y => Λ.Lp i y (u y) (grad u y)) x :=
    integrable_of_cs (hη.continuous.mul (continuous_finsetSum _ fun i _ => pd_continuous (hV i) i))
      hηc.mul_right
  simp only [mul_sub]
  rw [integral_sub h3 h4, ibp_div hη hηc hV, δA, integral_add h1 h2, sub_neg_eq_add]
  congr 1
  · congr 1; funext x; ring
  · congr 1; funext x; exact Finset.sum_congr rfl fun i _ => by ring

/-- Euler–Lagrange: stationarity of the action under every test variation is equivalent to the pointwise
equation L_u = div L_p (for C¹ u with C¹ flux L_p(·, u, ∇u)). -/
theorem euler_lagrange (Λ : Lag n) {u : E n → ℝ} (hu : ContDiff ℝ 1 u)
    (hV : ∀ i, ContDiff ℝ 1 fun y => Λ.Lp i y (u y) (grad u y)) :
    (∀ η, IsTest η → HasDerivAt (dA Λ u η) 0 0) ↔
      ∀ x, Λ.Lu x (u x) (grad u x) = dvg (fun i y => Λ.Lp i y (u y) (grad u y)) x := by
  have hgu := grad_continuous hu
  have hg : Continuous fun x => Λ.Lu x (u x) (grad u x) - dvg (fun i y => Λ.Lp i y (u y) (grad u y)) x :=
    (Λ.cont_u.comp (continuous_id.prodMk (hu.continuous.prodMk hgu))).sub
      (continuous_finsetSum _ fun i _ => pd_continuous (hV i) i)
  constructor
  · intro h x
    have := fund hg (fun η hη => by
      rw [← first_variation_ibp Λ hu hη.c1 hη.2 hV]
      exact (gateaux Λ hu hη.c1 hη.2).unique (h η hη))
    exact sub_eq_zero.1 (congrFun this x)
  · intro h η hη
    have := gateaux Λ hu hη.c1 hη.2
    rwa [first_variation_ibp Λ hu hη.c1 hη.2 hV, show (fun x => η x * (Λ.Lu x (u x) (grad u x) -
      dvg (fun i y => Λ.Lp i y (u y) (grad u y)) x)) = fun _ => 0 from funext fun x => by
        rw [h x, sub_self, mul_zero], integral_zero] at this

end Entropic.Var
