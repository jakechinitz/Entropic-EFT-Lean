import Mathlib

/-! Finite-contact algebra and bounds. These certificates do not derive a
physical bath, a desired halo distribution, or a full multistream action. -/
noncomputable section
open scoped BigOperators
namespace EffectiveContact

theorem gated_current_regular (J lam theta Vp A B : ℝ) (hl : lam ≠ 0) :
    -theta*J-Vp*A*(J/lam)^2-B*(J/lam) =
      -(theta+Vp*A*J/lam^2+B/lam)*J := by field_simp; ring

theorem power_gate_factor (v B : ℝ) : (B*v)*v=v^2*B := by ring

theorem resting_gate (B : ℝ) : (0:ℝ)^2*B=0 ∧ B*(0:ℝ)=0 := by simp

theorem contact_energy_ledger (P W Q : ℝ) (h : P=W-Q) : -W+P+Q=0 := by linarith

theorem work_per_event (Eold Enew theta logratio : ℝ) :
    (Enew-Eold+theta*logratio)-theta*logratio=Enew-Eold := by ring

theorem insufficient_supply_bound (K rho rho0 A w w0 : ℝ)
    (hA : 0 < A) (hfloor : K ≤ rho) (hledger : rho+A*w=rho0+A*w0) :
    w ≤ w0+(rho0-K)/A := by
  have hb : w-w0 ≤ (rho0-K)/A := by
    apply (le_div_iff₀ hA).mpr
    nlinarith
  linarith

theorem resting_endpoint (K rho0 A w w0 : ℝ)
    (hA : A ≠ 0) (hledger : K+A*w=rho0+A*w0) :
    w=w0+(rho0-K)/A := by
  field_simp; nlinarith

theorem local_rate_nonnegative (g nu target Z : ℝ)
    (hg : 0 ≤ g) (hn : 0 ≤ nu) (ht : 0 ≤ target) (hZ : 0 < Z) :
    0 ≤ g*nu*target/Z := by positivity

theorem contact_stationary (nu target Z a : ℝ) (hZ : Z ≠ 0) :
    nu*(target/Z*(a*Z)-a*target)=0 := by field_simp; ring

theorem local_detailed_balance (g nu hi hj Z : ℝ) :
    hi*(g*nu*hj/Z)=hj*(g*nu*hi/Z) := by ring

theorem local_population_conserved {ι : Type*} [Fintype ι]
    (h f : ι → ℝ) (nu Z : ℝ) (hZ : Z ≠ 0) (hs : ∑ i,h i=Z) :
    ∑ i, nu*(h i/Z*(∑ j,f j)-f i)=0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, ← Finset.sum_div, hs]
  field_simp <;> ring

theorem zero_population_inward (nu h Z mass : ℝ)
    (hn : 0 ≤ nu) (hh : 0 ≤ h) (hZ : 0 < Z) (hm : 0 ≤ mass) :
    0 ≤ nu*(h/Z*mass-0) := by
  simp only [sub_zero]
  exact mul_nonneg hn (mul_nonneg (div_nonneg hh hZ.le) hm)

theorem pair_flux_cancels (c x y : ℝ) : c*(y-x)+c*(x-y)=0 := by ring

theorem pair_quadratic_dissipation (c x y : ℝ) (hc : 0 ≤ c) :
    x*(c*(y-x))+y*(c*(x-y)) ≤ 0 := by
  have hh : 0 ≤ c*(x-y)^2 := mul_nonneg hc (sq_nonneg _)
  nlinarith

theorem reciprocal_impulse (p1 p2 kick : ℝ) : (p1+kick)+(p2-kick)=p1+p2 := by ring

theorem central_impulse_angular (x y z px py pz a : ℝ) :
    y*(pz+a*z)-z*(py+a*y)=y*pz-z*py ∧
    z*(px+a*x)-x*(pz+a*z)=z*px-x*pz ∧
    x*(py+a*y)-y*(px+a*x)=x*py-y*px := by
  constructor
  · ring
  · constructor <;> ring

theorem protected_pair_observable (qi qj flux : ℝ) (hq : qi=qj) :
    qi*(-flux)+qj*flux=0 := by rw [hq]; ring

theorem protected_noise (qdotb weight : ℝ) (h : qdotb=0) : weight*qdotb^2=0 := by rw [h]; ring

theorem weighted_floor (w rho1 rho2 K : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (h1 : K ≤ rho1) (h2 : K ≤ rho2) : K ≤ w*rho1+(1-w)*rho2 := by
  have ha := mul_nonneg hw0 (sub_nonneg.mpr h1)
  have hb := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr h2)
  nlinarith

theorem admissible_event_floor (rho work K : ℝ) (h : work ≤ rho-K) : K ≤ rho-work := by linarith

theorem frozen_clock_coupling_zero (nu h Z : ℝ) : (0:ℝ)^2*nu*h/Z=0 := by simp

theorem sufficient_residual_energy (rho0 K A p w0 : ℝ)
    (h : A*(p-w0) ≤ rho0-K) : K ≤ rho0-A*(p-w0) := by linarith

theorem symmetric_edge_gate (v0 v1 : ℝ) : v0*v1=v1*v0 := by ring

theorem edge_gate_probability (v0 v1 : ℝ)
    (h0 : 0 ≤ v0) (h1 : v0 ≤ 1) (h2 : 0 ≤ v1) (h3 : v1 ≤ 1) :
    0 ≤ v0*v1 ∧ v0*v1 ≤ 1 := by
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]

theorem joint_transition_energy (E Enew U bath W Q : ℝ)
    (h : W=Enew-E+Q) : Enew+(U-W)+(bath+Q)=E+U+bath := by rw [h]; ring

theorem work_invariant (U Gold Gnew : ℝ) :
    (U-(Gnew-Gold))+Gnew=U+Gold := by ring

theorem positive_edge_form (c xr xi yr yi : ℝ) (hc : 0 ≤ c) :
    0 ≤ c*(xr^2+xi^2+yr^2+yi^2-2*(xr*yr+xi*yi)) := by
  have h : 0 ≤ c*((xr-yr)^2+(xi-yi)^2) := by positivity
  nlinarith

theorem least_trace_positive_completion (d1 d2 c : ℝ)
    (h1 : 0 ≤ d1) (h2 : 0 ≤ d2) (hc : 0 ≤ c)
    (hdet : c^2 ≤ d1*d2) : 2*c ≤ d1+d2 := by
  nlinarith [sq_nonneg (d1-d2)]

theorem thermal_floor (rho eth K : ℝ) (h : K ≤ rho) (ht : 0 ≤ eth) :
    K ≤ rho+eth := by linarith

theorem thermal_enthalpy (rho p h eth gamma : ℝ) (hh : rho+p=h) :
    (rho+eth)+(p+(gamma-1)*eth)=h+gamma*eth := by nlinarith

theorem mixed_sound_speed (h0 ht c0 ct : ℝ)
    (h0n : 0 ≤ h0) (htn : 0 ≤ ht) (hpos : 0 < h0+ht)
    (c0n : 0 ≤ c0) (c0u : c0 ≤ 1) (ctn : 0 ≤ ct) (ctu : ct ≤ 1) :
    0 ≤ (h0*c0+ht*ct)/(h0+ht) ∧ (h0*c0+ht*ct)/(h0+ht) ≤ 1 := by
  constructor
  · positivity
  · apply (div_le_one hpos).mpr
    nlinarith [mul_nonneg h0n (sub_nonneg.mpr c0u),mul_nonneg htn (sub_nonneg.mpr ctu)]

theorem enthalpy_gate_bound (h0 ht lam : ℝ)
    (h0n : 0 ≤ h0) (htn : 0 ≤ ht) (hl : 0 < lam) (hh : h0 ≤ lam) :
    0 ≤ (h0+ht)/(lam+ht) ∧ (h0+ht)/(lam+ht) ≤ 1 := by
  have hd : 0 < lam+ht := by linarith
  exact ⟨div_nonneg (by linarith) hd.le,(div_le_one hd).mpr (by linarith)⟩

theorem cold_gate_limit (lam v : ℝ) (hl : lam ≠ 0) :
    (lam*v^2+0)/(lam+0)=v^2 := by field_simp [hl] <;> ring

theorem warm_power_fractional_rate (n mu lam ht B : ℝ) (hm : mu ≠ 0)
    (hd : lam+ht ≠ 0) :
    ((n*mu)/(lam+ht)*B)/mu=n*B/(lam+ht) := by field_simp [hm, hd] <;> ring

theorem warm_current_regular (n lam theta Vp A B D : ℝ) (hl : lam ≠ 0) :
    -theta*n-Vp*A*(n/lam)^2-n*B/D =
      -(theta+Vp*A*n/lam^2+B/D)*n := by field_simp; ring

theorem thermal_observer_floor (rho h w2 K : ℝ)
    (hr : K ≤ rho) (hh : 0 ≤ h) (hw : 1 ≤ w2) :
    K ≤ rho+h*(w2-1) := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hw)]

end EffectiveContact
