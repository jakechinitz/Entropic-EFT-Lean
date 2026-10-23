import Mathlib

/-! An analytic expanding, actively exchanging homogeneous Einstein solution.
Units: 8 pi G = 1, c = 1, spatial curvature = 0. D is the total dust density;
b is a separately conserved positive baryon component; C = D-b is the donor.
The source Q is strictly positive for t >= 0 and V starts at zero.
The donor branch is valid locally, before its first depletion. This file does
not assert positivity of C for all future time, or solve the inhomogeneous PDE.
-/
-- Ported from Lean 4.19: each derivative identity tries a short list of closers, since
-- `convert ... using 1` also leaves the function-equality goal in 4.35.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section
namespace Entropic.Compatibility.Expanding

def e (t : ℝ) := Real.exp (-t)
def H (t : ℝ) := 1/8 + e t/24
def D (t : ℝ) := e t/12
def V (t : ℝ) := 3*(H t)^2-D t
def Q (t : ℝ) := D t*(1-3*H t)
def a (t : ℝ) := Real.exp (t/8+(1-e t)/24)
def baryon (eps t : ℝ) := eps/(12*(1+eps))*Real.exp (-3*(t/8+(1-e t)/24))
def donor (eps t : ℝ) := D t-baryon eps t

theorem e_deriv (t : ℝ) : HasDerivAt e (-e t) t := by
  convert ((hasDerivAt_id t).neg).exp using 1 <;> first | rfl | simp [e]

theorem H_deriv (t : ℝ) : HasDerivAt H (-D t/2) t := by
  convert ((e_deriv t).div_const 24).const_add (1/8) using 1 <;> first | rfl | ring1 | (simp only [H,D]; ring1) | (funext x; simp only [H,D, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem D_deriv (t : ℝ) : HasDerivAt D (-D t) t := by
  convert (e_deriv t).div_const 12 using 1 <;> first | rfl | ring1 | (simp only [D]; ring1) | (funext x; simp only [D, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem loga_deriv (t : ℝ) : HasDerivAt (fun x => x/8+(1-e x)/24) (H t) t := by
  convert ((hasDerivAt_id t).div_const 8).add (((e_deriv t).const_sub 1).div_const 24) using 1 <;> first | rfl | ring1 | (simp only [H]; ring1) | (funext x; simp only [H, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem scale_deriv (t : ℝ) : HasDerivAt a (H t*a t) t := by
  convert (loga_deriv t).exp using 1 <;> first | rfl | ring1 | (simp only [a]; ring1) | (funext x; simp only [a, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem vacuum_deriv (t : ℝ) : HasDerivAt V (Q t) t := by
  convert (((H_deriv t).pow 2).const_mul 3).sub (D_deriv t) using 1 <;> first | rfl | ring1 | (simp only [V,Q]; ring1) | (funext x; simp only [V,Q, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem baryon_deriv (eps t : ℝ) :
    HasDerivAt (baryon eps) (-3*H t*baryon eps t) t := by
  convert (((loga_deriv t).const_mul (-3)).exp).const_mul (eps/(12*(1+eps))) using 1 <;> first | rfl | ring1 | (simp only [baryon]; ring1) | (funext x; simp only [baryon, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem donor_deriv (eps t : ℝ) :
    HasDerivAt (donor eps) (-3*H t*donor eps t-Q t) t := by
  convert (D_deriv t).sub (baryon_deriv eps t) using 1 <;> first | rfl | ring1 | (simp only [donor,Q]; ring1) | (funext x; simp only [donor,Q, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem friedmann (eps t : ℝ) : 3*(H t)^2=baryon eps t+donor eps t+V t := by
  dsimp [donor,V]; ring

theorem raychaudhuri (eps t : ℝ) :
    deriv H t = -(baryon eps t+donor eps t)/2 := by
  rw [(H_deriv t).deriv]; dsimp [donor]; ring

theorem total_conservation (eps t : ℝ) :
    deriv (baryon eps) t+deriv (donor eps) t+deriv V t+
      3*H t*(baryon eps t+donor eps t)=0 := by
  rw [(baryon_deriv eps t).deriv, (donor_deriv eps t).deriv, (vacuum_deriv t).deriv]
  ring

theorem expansion_positive (t : ℝ) : 0 < H t ∧ 0 < a t := by
  have he := Real.exp_pos (-t)
  constructor
  · dsimp [H,e]; positivity
  · exact Real.exp_pos _

theorem source_positive {t : ℝ} (ht : 0 ≤ t) : 0 < Q t := by
  have he := Real.exp_pos (-t)
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd : 0 < D t := by dsimp [D,e]; positivity
  apply mul_pos hd
  dsimp [H,e]; linarith

theorem initial_conditions (eps : ℝ) (he : 0 < eps) :
    a 0=1 ∧ V 0=0 ∧ 0 < baryon eps 0 ∧ 0 < donor eps 0 ∧
    donor eps 0=baryon eps 0/eps := by
  have hz : 1+eps ≠ 0 := by positivity
  have hc : donor eps 0=1/(12*(1+eps)) := by
    norm_num [donor,D,e,baryon]; field_simp; ring
  refine ⟨by norm_num [a,e], by norm_num [V,H,D,e], ?_, ?_, ?_⟩
  · norm_num [baryon,e]; positivity
  · rw [hc]; positivity
  · rw [hc]; norm_num [baryon,e]; field_simp

theorem vacuum_nonnegative {t : ℝ} (ht : 0 ≤ t) : 0 ≤ V t := by
  have he := Real.exp_pos (-t)
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hf : V t = (1-e t)*(9-e t)/192 := by dsimp [V,H,D]; ring
  rw [hf]
  apply div_nonneg _ (by norm_num)
  apply mul_nonneg <;> dsimp [e] <;> linarith

-- Exact same initial formation ratio as the galactic epsilon branch.
-- Existence of a neighborhood with a positive donor is a consequence of the
-- explicit solution and continuity, not an assumed positivity condition.
theorem donor_positive_near_origin (eps : ℝ) (he : 0 < eps) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ t, |t| < radius → 0 < donor eps t := by
  have hc : ContinuousAt (donor eps) 0 := (donor_deriv eps 0).continuousAt
  have hp := (initial_conditions eps he).2.2.2.1
  have ev : ∀ᶠ t in nhds (0:ℝ), 0 < donor eps t := hc.eventually (lt_mem_nhds hp)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp ev
  refine ⟨r, hr, ?_⟩
  intro t ht
  apply hb
  simpa [Metric.mem_ball, Real.dist_eq] using ht

-- The donor's logarithmic depletion is the paper's release fraction.
-- It obeys the exponential allocation exactly wherever the donor is positive.
def releasedFraction (eta eps t : ℝ) :=
  -Real.log ((a t)^3*donor eps t/donor eps 0)/eta

theorem fraction_zero (eta eps : ℝ) (he : 0 < eps) : releasedFraction eta eps 0=0 := by
  have hp := (initial_conditions eps he).2.2.2.1
  simp [releasedFraction, a, e, hp.ne']

theorem allocation_identity (eta eps t : ℝ) (hEta : eta ≠ 0)
    (hEps : 0 < eps) (hC : 0 < donor eps t) :
    (a t)^3*donor eps t = donor eps 0*Real.exp (-eta*releasedFraction eta eps t) := by
  have h0 := (initial_conditions eps hEps).2.2.2.1
  have hp : 0 < (a t)^3*donor eps t/donor eps 0 := by
    exact div_pos (mul_pos (pow_pos (expansion_positive t).2 _) hC) h0
  have harg : -eta*releasedFraction eta eps t =
      Real.log ((a t)^3*donor eps t/donor eps 0) := by
    dsimp [releasedFraction]; field_simp
  rw [harg, Real.exp_log hp]
  field_simp

def comoving (eps t : ℝ) := (a t)^3*donor eps t

theorem comoving_deriv (eps t : ℝ) :
    HasDerivAt (comoving eps) (-(a t)^3*Q t) t := by
  convert ((scale_deriv t).pow 3).mul (donor_deriv eps t) using 1 <;> first | rfl | ring1 | (simp only [comoving]; ring1) | (funext x; simp only [comoving, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]; ring1) | (funext x; rfl) | (norm_num [Pi.pow_apply, Pi.mul_apply]; ring1)

theorem fraction_deriv (eta eps t : ℝ) (hEta : eta ≠ 0) (hEps : 0 < eps)
    (hC : 0 < donor eps t) :
    HasDerivAt (releasedFraction eta eps) (Q t/(eta*donor eps t)) t := by
  have h0 := (initial_conditions eps hEps).2.2.2.1
  have ha := (expansion_positive t).2
  have hp : comoving eps t/donor eps 0 ≠ 0 := by
    exact (div_pos (mul_pos (pow_pos ha _) hC) h0).ne'
  convert ((((comoving_deriv eps t).div_const (donor eps 0)).log hp).neg).div_const eta using 1
  all_goals try (first | rfl | (funext x; rfl))
  dsimp [comoving]
  field_simp [hEta, h0.ne', hC.ne', ha.ne']

theorem comoving_decreases (eps : ℝ) : AntitoneOn (comoving eps) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t _; exact (comoving_deriv eps t).continuousAt.continuousWithinAt
  · intro t _; exact (comoving_deriv eps t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 0 ≤ t := (show 0 < t by simpa using ht).le
    rw [(comoving_deriv eps t).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_pos (expansion_positive t).2 _).le)
      (source_positive ht').le

theorem fraction_nonnegative (eta eps t : ℝ) (hEta : 0 < eta) (hEps : 0 < eps)
    (ht : 0 ≤ t) (hC : 0 < donor eps t) : 0 ≤ releasedFraction eta eps t := by
  have h0 := (initial_conditions eps hEps).2.2.2.1
  have hm := comoving_decreases eps (by simp) ht ht
  have ha0 : a 0=1 := (initial_conditions eps hEps).1
  have hu : (a t)^3*donor eps t/donor eps 0 ≤ 1 := by
    apply (div_le_one h0).mpr
    simpa [comoving,ha0] using hm
  have hp : 0 < (a t)^3*donor eps t/donor eps 0 :=
    div_pos (mul_pos (pow_pos (expansion_positive t).2 _) hC) h0
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hp.le hu)) hEta.le

-- A positive-duration interval with every release fraction in [0,1).
theorem admissible_interval (eta eps : ℝ) (hEta : 0 < eta) (hEps : 0 < eps) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ t, 0 ≤ t → t < radius →
      0 < donor eps t ∧ 0 ≤ releasedFraction eta eps t ∧ releasedFraction eta eps t < 1 := by
  have h0 := (initial_conditions eps hEps).2.2.2.1
  have hc := (fraction_deriv eta eps 0 hEta.ne' hEps h0).continuousAt
  have hf : releasedFraction eta eps 0 < 1 := by rw [fraction_zero eta eps hEps]; norm_num
  have ev := hc.eventually (gt_mem_nhds hf)
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp ev
  obtain ⟨s,hs,hCs⟩ := donor_positive_near_origin eps hEps
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro t ht htr
  have habs : |t|=t := abs_of_nonneg ht
  have hCt := hCs t (by rw [habs]; exact lt_of_lt_of_le htr (min_le_right _ _))
  refine ⟨hCt, fraction_nonnegative eta eps t hEta hEps ht hCt, ?_⟩
  apply hb
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero, habs]
  exact lt_of_lt_of_le htr (min_le_left _ _)

def unreleased (eta eps t : ℝ) := (1-releasedFraction eta eps t)*donor eps t
def retained (eta eps t : ℝ) := releasedFraction eta eps t*donor eps t
def releaseRate (eta eps t : ℝ) :=
  Q t/(eta*donor eps t*(1-releasedFraction eta eps t))

theorem components_sum (eta eps t : ℝ) :
    unreleased eta eps t+retained eta eps t=donor eps t := by
  dsimp [unreleased,retained]; ring

theorem unreleased_equation (eta eps t : ℝ) (hEta : 0 < eta) (hEps : 0 < eps)
    (hC : 0 < donor eps t) :
    HasDerivAt (unreleased eta eps)
      (-3*H t*unreleased eta eps t-Q t/eta-
        unreleased eta eps t/donor eps t*Q t) t := by
  convert ((fraction_deriv eta eps t hEta.ne' hEps hC).const_sub 1).mul (donor_deriv eps t) using 1
  all_goals try (first | rfl | (funext x; rfl))
  dsimp [unreleased]
  field_simp [hEta.ne',hC.ne']
  ring

theorem retained_equation (eta eps t : ℝ) (hEta : 0 < eta) (hEps : 0 < eps)
    (hC : 0 < donor eps t) :
    HasDerivAt (retained eta eps)
      (-3*H t*retained eta eps t+Q t/eta-retained eta eps t/donor eps t*Q t) t := by
  convert (fraction_deriv eta eps t hEta.ne' hEps hC).mul (donor_deriv eps t) using 1
  all_goals try (first | rfl | (funext x; rfl))
  dsimp [retained]
  field_simp [hEta.ne',hC.ne']
  ring

theorem rate_matches (eta eps t : ℝ) (hEta : 0 < eta) (hC : 0 < donor eps t)
    (hF : releasedFraction eta eps t < 1) :
    releaseRate eta eps t*unreleased eta eps t=Q t/eta := by
  have hf : 1-releasedFraction eta eps t ≠ 0 := by linarith
  dsimp [releaseRate,unreleased]
  field_simp [hEta.ne',hC.ne',hf]

-- The very same active Einstein solution fits the unchanged dust branch of
-- the new depletion action, for a positive interval and a fixed positive K.
theorem depletion_compatible_interval (eps : ℝ) (hEps : 0 < eps) :
    ∃ K radius : ℝ, 0 < K ∧ 0 < radius ∧ ∀ t, |t| < radius →
      0 < K-V t ∧ 3*(K-V t) < donor eps t := by
  let K := donor eps 0/6
  have hC := (initial_conditions eps hEps).2.2.2.1
  have hV := (initial_conditions eps hEps).2.1
  have hK : 0 < K := by dsimp [K]; positivity
  have ev1 : ∀ᶠ t in nhds (0:ℝ), V t < K :=
    (vacuum_deriv 0).continuousAt.eventually (gt_mem_nhds (by rw [hV]; exact hK))
  have hm : ContinuousAt (fun t => donor eps t-3*(K-V t)) 0 :=
    (donor_deriv eps 0).continuousAt.sub
      (continuousAt_const.mul (continuousAt_const.sub (vacuum_deriv 0).continuousAt))
  have hm0 : 0 < donor eps 0-3*(K-V 0) := by rw [hV]; dsimp [K]; linarith
  have ev2 := hm.eventually (lt_mem_nhds hm0)
  have ev : ∀ᶠ t in nhds (0:ℝ), 0 < K-V t ∧ 3*(K-V t)<donor eps t := by
    filter_upwards [ev1,ev2] with t ht1 ht2
    constructor <;> linarith
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp ev
  refine ⟨K,r,hK,hr,?_⟩
  intro t ht
  apply hb
  simpa [Metric.mem_ball, Real.dist_eq] using ht

theorem fraction_positive (eta eps t : ℝ) (hEta : 0 < eta) (hEps : 0 < eps)
    (ht : 0 < t) (hC : 0 < donor eps t) : 0 < releasedFraction eta eps t := by
  have hm : StrictAntiOn (comoving eps) (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    · intro x _; exact (comoving_deriv eps x).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 ≤ x := (show 0 < x by simpa using hx).le
      rw [(comoving_deriv eps x).deriv]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (pow_pos (expansion_positive x).2 _))
        (source_positive hx')
  have h0 := (initial_conditions eps hEps).2.2.2.1
  have ha0 := (initial_conditions eps hEps).1
  have hu : (a t)^3*donor eps t/donor eps 0 < 1 := by
    apply (div_lt_one h0).mpr
    simpa [comoving,ha0] using hm (by simp) ht.le ht
  have hp : 0 < (a t)^3*donor eps t/donor eps 0 :=
    div_pos (mul_pos (pow_pos (expansion_positive t).2 _) hC) h0
  exact div_pos (neg_pos.mpr (Real.log_neg hp hu)) hEta

theorem baryon_comoving (eps t : ℝ) : (a t)^3*baryon eps t=baryon eps 0 := by
  unfold a baryon
  rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
  simp [e]
  <;> ring_nf
  <;> simp

theorem physical_allocation (eta eps t : ℝ) (hEta : eta ≠ 0) (hEps : 0 < eps)
    (hC : 0 < donor eps t) :
    donor eps t=(baryon eps t/eps)*Real.exp (-eta*releasedFraction eta eps t) := by
  have h := allocation_identity eta eps t hEta hEps hC
  have hForm := (initial_conditions eps hEps).2.2.2.2
  have hB := baryon_comoving eps t
  have ha : a t ≠ 0 := (expansion_positive t).2.ne'
  rw [hForm, ← hB] at h
  apply (mul_left_cancel₀ (pow_ne_zero 3 ha))
  calc
    (a t)^3*donor eps t = ((a t)^3*baryon eps t/eps)*Real.exp (-eta*releasedFraction eta eps t) := h
    _ = (a t)^3*(baryon eps t/eps*Real.exp (-eta*releasedFraction eta eps t)) := by ring

end Entropic.Compatibility.Expanding
