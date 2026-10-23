import Entropic.Completion.GlobalSpatial

/-! Common local release fields in the global inhomogeneous solution.
Gamma=H and F=1-exp(-s); local q=H*u need NOT equal the uniform Q/eta.
The homogeneous reference a=d=0 does satisfy Q=eta*q_background.
This distinction is required by the manuscript O.3 background prescription. -/
noncomputable section
set_option linter.unnecessarySeqFocus false
namespace Entropic.Completion.GlobalRelease
open GlobalBackground GlobalSpatial

def unreleased (eta eps a d s : ℝ) := (1-F s)*donor eta eps a d s
def retained (eta eps a d s : ℝ) := F s*donor eta eps a d s
def localQ (eta eps a d s : ℝ) := H eta eps s*unreleased eta eps a d s

theorem baryon_deriv (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    HasDerivAt (baryon eta eps a d)
      (-theta eta eps a d s*baryon eta eps a d s/H eta eps s) s := by
  have hj := (J_positive eta eps a d s he hp ha hd hs).ne'
  have hh := (H_positive eta eps s he hp hs).ne'
  convert (hasDerivAt_const s (baryon0 eta eps a d)).div (volume_deriv eta eps a d s he hp ha hd hs) hj using 1 <;> (try funext x) <;>
    (try dsimp [baryon]) <;> field_simp <;> ring

theorem donor_deriv (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    HasDerivAt (donor eta eps a d)
      (-theta eta eps a d s*donor eta eps a d s/H eta eps s-sourceS eta s) s := by
  convert (density_deriv eta eps a d s he hp ha hd hs).sub (baryon_deriv eta eps a d s he hp ha hd hs) using 1 <;> (try funext x) <;>
    (try dsimp [donor]) <;> ring

theorem local_balances (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) (hc : donor eta eps a d s ≠ 0) :
    H eta eps s*deriv (unreleased eta eps a d) s+theta eta eps a d s*unreleased eta eps a d s=
      -localQ eta eps a d s-unreleased eta eps a d s*Q eta eps s/donor eta eps a d s ∧
    H eta eps s*deriv (retained eta eps a d) s+theta eta eps a d s*retained eta eps a d s=
      localQ eta eps a d s-retained eta eps a d s*Q eta eps s/donor eta eps a d s := by
  have hh := (H_positive eta eps s he hp hs).ne'
  have du := ((F_deriv s).const_sub 1).mul (donor_deriv eta eps a d s he hp ha hd hs)
  have dr := (F_deriv s).mul (donor_deriv eta eps a d s he hp ha hd hs)
  change HasDerivAt (unreleased eta eps a d) _ s at du
  change HasDerivAt (retained eta eps a d) _ s at dr
  rw [du.deriv,dr.deriv]
  dsimp [unreleased,retained,localQ,Q,F]
  constructor <;> field_simp <;> ring

theorem same_stock_sources_metric (eta eps a d s : ℝ) :
    (2/3*alpha eta eps a s)^2+
      2*(2/3*alpha eta eps a s)*(alpha eta eps d s-alpha eta eps a s/3)=
      baryon eta eps a d s+unreleased eta eps a d s+retained eta eps a d s+V eta s := by
  dsimp [unreleased,retained,donor,rho]; ring

theorem positive_components (eta eps delta a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (ha1 : a ≤ delta) (hd1 : d ≤ delta) (hs : 0 ≤ s) :
    0 < baryon eta eps a d s ∧ 0 < unreleased eta eps a d s ∧ 0 ≤ retained eta eps a d s := by
  have hc := donor_positive eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs
  have hj := J_positive eta eps a d s he hp ha hd hs
  have hH0 := H_positive eta eps 0 he hp (by norm_num)
  have hrho : 0 < rho eta eps a d 0 := by rw [initial_density eta eps a d he hp]; positivity
  have hb : 0 < baryon eta eps a d s := by dsimp [baryon,baryon0]; positivity
  obtain ⟨hf,hf1⟩ := fraction_bounds s hs
  exact ⟨hb,mul_pos (sub_pos.mpr hf1) hc,mul_nonneg hf hc.le⟩

theorem positive_retained (eta eps delta a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (ha1 : a ≤ delta) (hd1 : d ≤ delta) (hs : 0 < s) : 0 < retained eta eps a d s := by
  have hc := donor_positive eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs.le
  have hf : 0 < F s := by
    dsimp [F]; have hh := Real.exp_lt_one_iff.mpr (show -s < 0 by linarith); linarith
  exact mul_pos hf hc

theorem reference_matches_background (eta eps s : ℝ) (he : 0 < eta) (hp : 0 < eps) (hs : 0 ≤ s) :
    donor eta eps 0 0 s=C eta s ∧ Q eta eps s=eta*localQ eta eps 0 0 s := by
  have hf := friedmann eta eps s he hp hs
  have h0 := initial_density eta eps 0 0 he hp
  have hj : J eta eps 0 0 s=1/E s := by simp [J,P]
  have hr : rho eta eps 0 0 s=b eps s+C eta s := by
    dsimp [rho,alpha,correction]; simp; nlinarith [hf]
  have hb0 : baryon0 eta eps 0 0=eps := by
    rw [baryon0,h0]
    have hz : 1+eps ≠ 0 := by positivity
    field_simp <;> ring <;> simp
  have hb : baryon eta eps 0 0 s=b eps s := by
    rw [baryon,hb0,hj]; simp [b,E,div_eq_mul_inv]
  have hc : donor eta eps 0 0 s=C eta s := by rw [donor,hr,hb]; ring
  refine ⟨hc,?_⟩
  dsimp [localQ,unreleased]; rw [hc]
  dsimp [Q,sourceS,F]; ring

theorem radial_contrast (eta eps delta : ℝ) (he : 0 < eta) (hp : 0 < eps) (hd : 0 < delta) :
    rho eta eps (h delta 2) (j delta 2) 0 < rho eta eps (h delta 1) (j delta 1) 0 := by
  rw [initial_density eta eps (h delta 2) (j delta 2) he hp,
    initial_density eta eps (h delta 1) (j delta 1) he hp]
  have hh := H_positive eta eps 0 he hp (by norm_num)
  norm_num [h,j]
  nlinarith [sq_pos_of_pos hd]


theorem alpha_strict_in_parameter (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (had : a < d) (hs : 0 ≤ s) : alpha eta eps a s < alpha eta eps d s := by
  have hpa := P_positive eta eps a s he hp ha hs
  have hpd := P_positive eta eps d s he hp (by linarith) hs
  have hE : 0 < E s := Real.exp_pos _
  have hq : correction eta eps a s < correction eta eps d s := by
    apply (div_lt_div_iff₀ hpa hpd).mpr
    dsimp [P]
    nlinarith [mul_pos (sub_pos.mpr had) hE]
  dsimp [alpha]; linarith

theorem global_radial_contrast (eta eps delta s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hd : 0 < delta) (hs : 0 ≤ s) :
    rho eta eps (h delta 2) (j delta 2) s < rho eta eps (h delta 1) (j delta 1) s := by
  have ha := alpha_strict_in_parameter eta eps (h delta 2) (h delta 1) s he hp
    (profile_bounds delta 2 hd (by norm_num)).1.le (by dsimp [h]; nlinarith) hs
  have hb := alpha_strict_in_parameter eta eps (j delta 2) (j delta 1) s he hp
    (profile_bounds delta 2 hd (by norm_num)).2.2.1.le (by dsimp [j]; nlinarith) hs
  have hh := H_positive eta eps s he hp hs
  have hE : 0 < E s := Real.exp_pos _
  have hap : 0 < alpha eta eps (h delta 2) s := by
    have hw := (profile_bounds delta 2 hd (by norm_num)).1
    have hP := P_positive eta eps (h delta 2) s he hp hw.le hs
    dsimp [alpha,correction]; positivity
  have hbp : 0 < alpha eta eps (j delta 2) s := by
    have hw := (profile_bounds delta 2 hd (by norm_num)).2.2.1
    have hP := P_positive eta eps (j delta 2) s he hp hw.le hs
    dsimp [alpha,correction]; positivity
  have hm := mul_lt_mul ha hb.le hbp (by linarith : 0 ≤ alpha eta eps (h delta 1) s)
  dsimp [rho]; nlinarith

end Entropic.Completion.GlobalRelease
