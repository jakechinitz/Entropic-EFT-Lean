import Entropic.Completion.GlobalBackground

/-! Global inhomogeneous extension of the same background V and H.
The spatial profile is h(r)=delta/(1+r), j=h+2r*h'/3, on r>0.
E-fold lapse is 1/H. These scalar identities and positivity estimates are
kernel checked; the tensor reduction is checked separately by metric_check.py.
This supplies a classical effective solution, not a microscopic continuum limit. -/
noncomputable section
set_option maxRecDepth 2000
set_option linter.unnecessarySeqFocus false
namespace Entropic.Completion.GlobalSpatial
open MeasureTheory
open GlobalBackground

def E (s : ℝ) := Real.exp (-3*s)
def weight (eta eps s : ℝ) := E s/H eta eps s
def I (eta eps s : ℝ) := ∫ z in (0:ℝ)..s, weight eta eps z
def P (eta eps a s : ℝ) := 1+a*I eta eps s
def correction (eta eps a s : ℝ) := a*E s/P eta eps a s
def alpha (eta eps a s : ℝ) := 3*H eta eps s/2+correction eta eps a s
def J (eta eps a d s : ℝ) := P eta eps a s*P eta eps d s/E s
def rho (eta eps a d s : ℝ) := 4/3*alpha eta eps a s*alpha eta eps d s-V eta s
def baryon0 (eta eps a d : ℝ) := eps/(1+eps)*rho eta eps a d 0
def baryon (eta eps a d s : ℝ) := baryon0 eta eps a d/J eta eps a d s
def donor (eta eps a d s : ℝ) := rho eta eps a d s-baryon eta eps a d s
def theta (eta eps a d s : ℝ) := alpha eta eps a s+alpha eta eps d s

theorem weight_integrable (eta eps s : ℝ) (he : 0 < eta) (hp : 0 < eps) (hs : 0 ≤ s) :
    IntervalIntegrable (weight eta eps) volume 0 s := by
  have hc : ContinuousOn (weight eta eps) (Set.Icc 0 s) := by
    apply ContinuousOn.div
    · unfold E; fun_prop
    · exact (H_continuous eta eps).continuousOn
    · intro z hz; exact (H_positive eta eps z he hp hz.1).ne'
  exact hc.intervalIntegrable_of_Icc hs

theorem I_deriv (eta eps s : ℝ) (he : 0 < eta) (hp : 0 < eps) (hs : 0 ≤ s) :
    HasDerivAt (I eta eps) (weight eta eps s) s := by
  have hc : ContinuousAt (weight eta eps) s := by
    apply ContinuousAt.div
    · unfold E; fun_prop
    · exact (H_continuous eta eps).continuousAt
    · exact (H_positive eta eps s he hp hs).ne'
  have hm : StronglyMeasurable (weight eta eps) := by
    apply Measurable.stronglyMeasurable
    exact (show Continuous E by unfold E; fun_prop).measurable.div (H_continuous eta eps).measurable
  exact intervalIntegral.integral_hasDerivAt_right (weight_integrable eta eps s he hp hs)
    hm.stronglyMeasurableAtFilter hc

theorem I_nonnegative (eta eps s : ℝ) (he : 0 < eta) (hp : 0 < eps) (hs : 0 ≤ s) :
    0 ≤ I eta eps s := by
  apply intervalIntegral.integral_nonneg hs
  intro z hz
  exact div_nonneg (Real.exp_pos _).le (H_positive eta eps z he hp hz.1).le

theorem P_positive (eta eps a s : ℝ) (he : 0 < eta) (hp : 0 < eps) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    0 < P eta eps a s := by
  have hi := I_nonnegative eta eps s he hp hs
  dsimp [P]; positivity

theorem E_deriv (s : ℝ) : HasDerivAt E (-3*E s) s := by
  convert (((hasDerivAt_id s).const_mul (-3)).exp) using 1 <;> (try funext x) <;> (try dsimp [E]) <;> ring

theorem correction_deriv (eta eps a s : ℝ) (he : 0 < eta) (hp : 0 < eps) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    HasDerivAt (correction eta eps a)
      (-3*correction eta eps a s-(correction eta eps a s)^2/H eta eps s) s := by
  have hP := (P_positive eta eps a s he hp ha hs).ne'
  have hH := (H_positive eta eps s he hp hs).ne'
  dsimp [P] at hP
  have hd := ((E_deriv s).const_mul a).div (((I_deriv eta eps s he hp hs).const_mul a).const_add 1) hP
  convert hd using 1 <;> (try funext x) <;> (try dsimp [correction,P,weight]) <;> field_simp <;> ring

theorem alpha_deriv (eta eps a s : ℝ) (he : 0 < eta) (hp : 0 < eps) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    HasDerivAt (alpha eta eps a) ((3/4*V eta s-(alpha eta eps a s)^2)/H eta eps s) s := by
  have hH := (H_positive eta eps s he hp hs).ne'
  have hf := friedmann eta eps s he hp hs
  have hd := ((H_deriv eta eps s he hp hs).const_mul (3/2)).add (correction_deriv eta eps a s he hp ha hs)
  convert hd using 1
  all_goals try (first | rfl | (funext x; rfl))
  · funext z; dsimp [alpha]; ring
  · dsimp [alpha]; field_simp; nlinarith [hf]

theorem radial_einstein (eta eps a s : ℝ) (he : 0 < eta) (hp : 0 < eps) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    2*H eta eps s*deriv (fun z => 2/3*alpha eta eps a z) s+
      3*(2/3*alpha eta eps a s)^2=V eta s := by
  rw [((alpha_deriv eta eps a s he hp ha hs).const_mul (2/3)).deriv]
  have hz := (H_positive eta eps s he hp hs).ne'
  field_simp <;> ring

theorem angular_einstein (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    H eta eps s*(deriv (fun z => 2/3*alpha eta eps a z) s+
      deriv (fun z => alpha eta eps d z-alpha eta eps a z/3) s)+
      (2/3*alpha eta eps a s)^2+(alpha eta eps d s-alpha eta eps a s/3)^2+
      (2/3*alpha eta eps a s)*(alpha eta eps d s-alpha eta eps a s/3)=V eta s := by
  rw [((alpha_deriv eta eps a s he hp ha hs).const_mul (2/3)).deriv,
    ((alpha_deriv eta eps d s he hp hd hs).fun_sub ((alpha_deriv eta eps a s he hp ha hs).div_const 3)).deriv]
  have hz := (H_positive eta eps s he hp hs).ne'
  field_simp <;> ring

theorem J_positive (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) : 0 < J eta eps a d s :=
  div_pos (mul_pos (P_positive eta eps a s he hp ha hs) (P_positive eta eps d s he hp hd hs)) (Real.exp_pos _)

theorem volume_deriv (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    HasDerivAt (J eta eps a d) (theta eta eps a d s*J eta eps a d s/H eta eps s) s := by
  have hP := (P_positive eta eps a s he hp ha hs).ne'
  have hD := (P_positive eta eps d s he hp hd hs).ne'
  have hH := (H_positive eta eps s he hp hs).ne'
  have hE := (Real.exp_pos (-3*s)).ne'
  dsimp [P] at hP hD
  have hP' : 1 + I eta eps s * a ≠ 0 := by rwa [mul_comm]
  have hD' : 1 + I eta eps s * d ≠ 0 := by rwa [mul_comm]
  have di := I_deriv eta eps s he hp hs
  convert ((((di.const_mul a).const_add 1).mul ((di.const_mul d).const_add 1)).div (E_deriv s) hE) using 1 <;> (try funext x) <;>
    (try dsimp [J,theta,alpha,correction,P,weight,E]) <;> field_simp <;> ring

theorem density_deriv (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    HasDerivAt (rho eta eps a d)
      (-theta eta eps a d s*rho eta eps a d s/H eta eps s-sourceS eta s) s := by
  have hH := (H_positive eta eps s he hp hs).ne'
  convert ((((alpha_deriv eta eps a s he hp ha hs).const_mul (4/3)).mul
    (alpha_deriv eta eps d s he hp hd hs)).sub (V_deriv eta s)) using 1 <;> (try funext x) <;>
    (try dsimp [rho,theta]) <;> field_simp <;> ring


theorem background_factorization (eta eps s : ℝ) :
    b eps s+C eta s=E s*(eps+Real.exp (-eta*F s)) := by
  dsimp [b,C,E]
  rw [show -3*s-eta*F s=(-3*s)+(-eta*F s) by ring,Real.exp_add]
  ring

theorem comoving_density (eta eps a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    J eta eps a d s*rho eta eps a d s=
      (eps+Real.exp (-eta*F s))*P eta eps a s*P eta eps d s+
      2*H eta eps s*(a+d+2*a*d*I eta eps s)+4/3*a*d*E s := by
  have hP := (P_positive eta eps a s he hp ha hs).ne'
  have hD := (P_positive eta eps d s he hp hd hs).ne'
  have hE : E s ≠ 0 := (Real.exp_pos _).ne'
  have hf := friedmann eta eps s he hp hs
  rw [background_factorization] at hf
  have hv : V eta s=3*(H eta eps s)^2-E s*(eps+Real.exp (-eta*F s)) := by linarith
  dsimp [J,rho,alpha,correction]
  rw [hv]
  dsimp [P] at *
  have hP' : 1 + I eta eps s * a ≠ 0 := by rwa [mul_comm]
  have hD' : 1 + I eta eps s * d ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

theorem initial_density (eta eps a d : ℝ) (he : 0 < eta) (hp : 0 < eps) :
    rho eta eps a d 0=eps+1+2*H eta eps 0*(a+d)+4/3*a*d := by
  have hf := friedmann eta eps 0 he hp (by norm_num)
  simp [b,C,F,V] at hf
  dsimp [rho,alpha,correction,P,I,E,V]
  norm_num
  nlinarith [hf]

def amplitudeBound (eta eps : ℝ) := eps/(1+eps)*(4*H eta eps 0+4/3)
def small (eta eps delta : ℝ) : Prop :=
  0 < delta ∧ delta ≤ 1 ∧ amplitudeBound eta eps*delta < Real.exp (-eta)/2

theorem small_exists (eta eps : ℝ) (he : 0 < eta) (hp : 0 < eps) :
    ∃ delta : ℝ, small eta eps delta := by
  have hh := H_positive eta eps 0 he hp (by norm_num)
  have hc : 0 < amplitudeBound eta eps := by dsimp [amplitudeBound]; positivity
  let delta := min 1 (Real.exp (-eta)/(4*amplitudeBound eta eps))
  have hd : 0 < delta := lt_min (by norm_num) (by positivity)
  have hle : delta ≤ Real.exp (-eta)/(4*amplitudeBound eta eps) := min_le_right _ _
  have hm := (le_div_iff₀ (show 0 < 4*amplitudeBound eta eps by positivity)).mp hle
  exact ⟨delta,hd,min_le_left _ _,by nlinarith [Real.exp_pos (-eta)]⟩

theorem comoving_donor_positive (eta eps delta a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (ha1 : a ≤ delta) (hd1 : d ≤ delta) (hs : 0 ≤ s) :
    Real.exp (-eta)/2 < J eta eps a d s*donor eta eps a d s := by
  have hj := J_positive eta eps a d s he hp ha hd hs
  have hH := H_positive eta eps s he hp hs
  have hH0 := H_positive eta eps 0 he hp (by norm_num)
  have hi := I_nonnegative eta eps s he hp hs
  have hP : 1 ≤ P eta eps a s := by dsimp [P]; nlinarith
  have hD : 1 ≤ P eta eps d s := by dsimp [P]; nlinarith
  have hprod : 1 ≤ P eta eps a s*P eta eps d s := by nlinarith
  have hfrac := fraction_bounds s hs
  have hex : Real.exp (-eta) ≤ Real.exp (-eta*F s) := Real.exp_le_exp.mpr (by nlinarith)
  have hmass := comoving_density eta eps a d s he hp ha hd hs
  have hmasslow : eps+Real.exp (-eta) ≤ J eta eps a d s*rho eta eps a d s := by
    have hx : 0 < eps+Real.exp (-eta*F s) := by positivity
    have hpterm := mul_le_mul_of_nonneg_left hprod hx.le
    have hterm : 0 ≤ 2*H eta eps s*(a+d+2*a*d*I eta eps s)+4/3*a*d*E s := by
      have hE : 0 < E s := Real.exp_pos _
      positivity
    nlinarith
  have hcoef : 0 < eps/(1+eps) := by positivity
  have had : a*d ≤ delta := by
    have had' := mul_le_mul ha1 hd1 hd hsmall.1.le
    nlinarith [hsmall.1,hsmall.2.1]
  have hsum : a+d ≤ 2*delta := by linarith
  have hbound : 2*H eta eps 0*(a+d)+4/3*a*d ≤ (4*H eta eps 0+4/3)*delta := by
    nlinarith
  have hbound2 := mul_le_mul_of_nonneg_left hbound hcoef.le
  have hb0 : baryon0 eta eps a d=eps+eps/(1+eps)*(2*H eta eps 0*(a+d)+4/3*a*d) := by
    rw [baryon0,initial_density eta eps a d he hp]
    have hn : 1+eps ≠ 0 := by positivity
    field_simp <;> ring
  have hid : J eta eps a d s*donor eta eps a d s=
      J eta eps a d s*rho eta eps a d s-baryon0 eta eps a d := by
    dsimp [donor,baryon]; field_simp <;> ring
  rw [hid,hb0]
  have hsm := hsmall.2.2
  dsimp [amplitudeBound] at hsm
  nlinarith

theorem donor_positive (eta eps delta a d s : ℝ) (he : 0 < eta) (hp : 0 < eps)
    (hsmall : small eta eps delta) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (ha1 : a ≤ delta) (hd1 : d ≤ delta) (hs : 0 ≤ s) : 0 < donor eta eps a d s := by
  have hj := J_positive eta eps a d s he hp ha hd hs
  have hc := comoving_donor_positive eta eps delta a d s he hp hsmall ha hd ha1 hd1 hs
  have hex := Real.exp_pos (-eta)
  nlinarith

def h (delta r : ℝ) := delta/(1+r)
def j (delta r : ℝ) := delta*(1+r/3)/(1+r)^2

theorem profile_bounds (delta r : ℝ) (hd : 0 < delta) (hr : 0 ≤ r) :
    0 < h delta r ∧ h delta r ≤ delta ∧ 0 < j delta r ∧ j delta r ≤ delta := by
  have hz : 0 < 1+r := by positivity
  have hz2 : 0 < (1+r)^2 := sq_pos_of_pos hz
  dsimp [h,j]
  refine ⟨by positivity,?_,by positivity,?_⟩
  · apply (div_le_iff₀ hz).mpr; nlinarith
  · apply (div_le_iff₀ hz2).mpr
    nlinarith [sq_nonneg r,mul_nonneg hd.le (sq_nonneg r)]

theorem radial_profile_relation (delta r : ℝ) (hr : 0 ≤ r) :
    j delta r=h delta r+(2*r/3)*deriv (h delta) r := by
  have hn : 1+r ≠ 0 := by positivity
  have hh : HasDerivAt (h delta) (-delta/(1+r)^2) r := by
    convert (hasDerivAt_const r delta).div ((hasDerivAt_id r).const_add 1) hn using 1 <;> (try funext x) <;>
      (try dsimp [h]) <;> ring
  rw [hh.deriv]; dsimp [h,j]; field_simp <;> ring

end Entropic.Completion.GlobalSpatial
