import Mathlib

/-! Explicit inhomogeneous, expanding spherical dust plus an increasing vacuum.
Units c=8*pi*G=1. R=r*A^(2/3), radial metric coefficient B^2/A^(2/3),
where B=A+(2r/3)*partial_r A. On A,B>0 this is a Lorentzian LTB chart.
The theorems below check the reduced Einstein equations and the same component
densities and exchange law. The tensor reduction is checked separately by SymPy;
this file does not formalize differential geometry or the native microscopic action.
-/
noncomputable section
set_option linter.unnecessarySeqFocus false
open MeasureTheory
namespace Entropic.Completion.Spatial

def U (t : ℝ) := Real.exp (t^3/12)
def W (t : ℝ) := Real.exp (-t^3/6)
def I (t : ℝ) := ∫ s in (0:ℝ)..t, W s
def Y (t : ℝ) := U t*I t
def Up (t : ℝ) := U t*(t^2/4)
def Yp (t : ℝ) := Up t*I t+U t*W t
def potential (t : ℝ) := t/2+t^4/16
def V (t : ℝ) := 2*t/3+t^4/12
def Q (t : ℝ) := 2/3+t^3/3
def h (r : ℝ) := 1-r^2/10
def j (r : ℝ) := 1-7*r^2/30
def A (r t : ℝ) := U t+h r*Y t
def B (r t : ℝ) := U t+j r*Y t
def Ap (r t : ℝ) := Up t+h r*Yp t
def Bp (r t : ℝ) := Up t+j r*Yp t
def alpha (r t : ℝ) := Ap r t/A r t
def beta (r t : ℝ) := Bp r t/B r t
def Htrans (r t : ℝ) := 2/3*alpha r t
def Hrad (r t : ℝ) := beta r t-alpha r t/3
def theta (r t : ℝ) := alpha r t+beta r t
def J (r t : ℝ) := A r t*B r t
def rho (r t : ℝ) := 4/3*alpha r t*beta r t-V t

theorem U_deriv (t : ℝ) : HasDerivAt U (Up t) t := by
  convert (((hasDerivAt_id t).pow 3).div_const 12).exp using 1 <;> (try funext x) <;> (try dsimp [U,Up]) <;> ring

theorem W_deriv (t : ℝ) : HasDerivAt W (-t^2/2*W t) t := by
  convert ((((hasDerivAt_id t).pow 3).neg).div_const 6).exp using 1 <;> (try funext x) <;> (try dsimp [W]) <;> ring

theorem I_deriv (t : ℝ) : HasDerivAt I (W t) t := by
  have hc : Continuous W := by unfold W; fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem Y_deriv (t : ℝ) : HasDerivAt Y (Yp t) t := by
  exact (U_deriv t).mul (I_deriv t)

theorem Up_deriv (t : ℝ) : HasDerivAt Up (potential t*U t) t := by
  convert (U_deriv t).mul (((hasDerivAt_id t).pow 2).div_const 4) using 1 <;> (try funext x) <;>
    (try dsimp [Up,potential]) <;> ring

theorem Yp_deriv (t : ℝ) : HasDerivAt Yp (potential t*Y t) t := by
  convert ((Up_deriv t).mul (I_deriv t)).add ((U_deriv t).mul (W_deriv t)) using 1 <;> (try funext x) <;>
    (try dsimp [Yp,Y,Up]) <;> ring

theorem A_deriv (r t : ℝ) : HasDerivAt (A r) (Ap r t) t :=
  (U_deriv t).add ((Y_deriv t).const_mul (h r))
theorem B_deriv (r t : ℝ) : HasDerivAt (B r) (Bp r t) t :=
  (U_deriv t).add ((Y_deriv t).const_mul (j r))

theorem Ap_deriv (r t : ℝ) : HasDerivAt (Ap r) (potential t*A r t) t := by
  convert (Up_deriv t).add ((Yp_deriv t).const_mul (h r)) using 1 <;> (try funext x) <;> (try dsimp [Ap,A]) <;> ring
theorem Bp_deriv (r t : ℝ) : HasDerivAt (Bp r) (potential t*B r t) t := by
  convert (Up_deriv t).add ((Yp_deriv t).const_mul (j r)) using 1 <;> (try funext x) <;> (try dsimp [Bp,B]) <;> ring

theorem alpha_deriv (r t : ℝ) (ha : A r t ≠ 0) :
    HasDerivAt (alpha r) (potential t-(alpha r t)^2) t := by
  convert (Ap_deriv r t).div (A_deriv r t) ha using 1 <;> (try funext x) <;> (try dsimp [alpha]) <;> field_simp <;> ring
theorem beta_deriv (r t : ℝ) (hb : B r t ≠ 0) :
    HasDerivAt (beta r) (potential t-(beta r t)^2) t := by
  convert (Bp_deriv r t).div (B_deriv r t) hb using 1 <;> (try funext x) <;> (try dsimp [beta]) <;> field_simp <;> ring

theorem vacuum_deriv (t : ℝ) : HasDerivAt V (Q t) t := by
  convert (((hasDerivAt_id t).const_mul 2).div_const 3).add (((hasDerivAt_id t).pow 4).div_const 12) using 1 <;> (try funext x) <;>
    (try dsimp [V,Q]) <;> ring

theorem source_positive (t : ℝ) (ht : 0 ≤ t) : 0 < Q t := by
  dsimp [Q]; positivity
theorem vacuum_nonnegative (t : ℝ) (ht : 0 ≤ t) : 0 ≤ V t := by
  dsimp [V]; positivity

theorem radial_relation (r t : ℝ) :
    B r t=A r t+(2*r/3)*deriv (fun s => A s t) r := by
  have hd : HasDerivAt (fun s => A s t) ((-r/5)*Y t) r := by
    convert (((((hasDerivAt_id r).pow 2).div_const 10).const_sub 1).mul_const (Y t)).const_add (U t) using 1 <;> (try funext x) <;>
      (try dsimp [A,h]) <;> ring
  rw [hd.deriv]; dsimp [B,A,h,j]; ring

theorem h_positive (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) : 0<h r ∧ 0<j r := by
  have hs : r^2 ≤ 1 := by nlinarith
  dsimp [h,j]; constructor <;> nlinarith

theorem AB_positive (r t : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 ≤ t) :
    0<A r t ∧ 0<B r t := by
  have hu : 0<U t := Real.exp_pos _
  have hi : 0 ≤ I t := intervalIntegral.integral_nonneg_of_forall ht (fun s => (Real.exp_pos _).le)
  have hy : 0 ≤ Y t := mul_nonneg hu.le hi
  obtain ⟨hh,hj⟩ := h_positive r hr hr1
  dsimp [A,B]; constructor <;> positivity

theorem expanding (r t : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : 0 ≤ t) :
    0 < Htrans r t ∧ 0 < theta r t := by
  obtain ⟨ha,hb⟩ := AB_positive r t hr hr1 ht
  obtain ⟨hh,hj⟩ := h_positive r hr hr1
  have hu : 0<U t := Real.exp_pos _
  have hw : 0<W t := Real.exp_pos _
  have hi : 0 ≤ I t := intervalIntegral.integral_nonneg_of_forall ht (fun s => (Real.exp_pos _).le)
  have hup : 0 ≤ Up t := by dsimp [Up]; positivity
  have hyp : 0<Yp t := by dsimp [Yp]; positivity
  have hap : 0<Ap r t := by dsimp [Ap]; positivity
  have hbp : 0<Bp r t := by dsimp [Bp]; positivity
  dsimp [Htrans,theta,alpha,beta]; constructor <;> positivity

theorem hamiltonian (r t : ℝ) :
    (Htrans r t)^2+2*Htrans r t*Hrad r t=rho r t+V t := by
  dsimp [Htrans,Hrad,rho]; ring

theorem radial_einstein (r t : ℝ) (ha : A r t ≠ 0) :
    2*deriv (Htrans r) t+3*(Htrans r t)^2=V t := by
  have hd := (alpha_deriv r t ha).const_mul (2/3)
  change HasDerivAt (Htrans r) _ t at hd
  rw [hd.deriv]; dsimp [Htrans,potential,V]; ring

theorem angular_einstein (r t : ℝ) (ha : A r t ≠ 0) (hb : B r t ≠ 0) :
    deriv (Htrans r) t+deriv (Hrad r) t+(Htrans r t)^2+
      (Hrad r t)^2+Htrans r t*Hrad r t=V t := by
  have hd := (alpha_deriv r t ha).const_mul (2/3)
  have he := (beta_deriv r t hb).sub ((alpha_deriv r t ha).div_const 3)
  change HasDerivAt (Htrans r) _ t at hd
  change HasDerivAt (Hrad r) _ t at he
  rw [hd.deriv,he.deriv]; dsimp [Htrans,Hrad,potential,V]; ring

theorem density_deriv (r t : ℝ) (ha : A r t ≠ 0) (hb : B r t ≠ 0) :
    HasDerivAt (rho r) (-theta r t*rho r t-Q t) t := by
  convert ((((alpha_deriv r t ha).const_mul (4/3)).mul (beta_deriv r t hb)).sub (vacuum_deriv t)) using 1 <;> (try funext x) <;>
    (try dsimp [rho,theta,potential,V]) <;> ring

theorem volume_deriv (r t : ℝ) (ha : A r t ≠ 0) (hb : B r t ≠ 0) :
    HasDerivAt (J r) (theta r t*J r t) t := by
  convert (A_deriv r t).mul (B_deriv r t) using 1 <;> (try funext x) <;>
    (try dsimp [J,theta,alpha,beta]) <;> field_simp <;> ring

theorem initial_geometry (r : ℝ) : A r 0=1 ∧ B r 0=1 ∧ J r 0=1 ∧
    rho r 0=4/3*h r*j r ∧ V 0=0 := by
  norm_num [A,B,J,rho,alpha,beta,Ap,Bp,U,Up,Y,Yp,I,V,W]

theorem inhomogeneous_core : rho 0 0=4/3 ∧ rho 1 0=23/25 ∧ rho 1 0<rho 0 0 := by
  have h0 := (initial_geometry 0).2.2.2.1
  have h1 := (initial_geometry 1).2.2.2.1
  norm_num [h,j] at h0 h1
  exact ⟨h0,h1,by rw [h0,h1]; norm_num⟩

end Entropic.Completion.Spatial
