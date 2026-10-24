import Mathlib

/-! Conditional microscopic-to-fluid identities and a finite weighted Schur
bound. The physical stock operator, pair kernel, continuum harmonic expansion,
and Euler--Poisson solution theory are not supplied by these declarations.
The near-floor identities distinguish the source current from a massive halo.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.MicroEnvelope3D

-- Thermodynamic pressure rho*e'(rho)-e(rho) for a supplied quadratic energy.
theorem quadratic_pair_pressure (rho zeta : ℝ) :
    rho*(2*zeta*rho)-zeta*rho^2 = zeta*rho^2 := by ring

theorem linear_rest_energy_cancels_from_pressure (rho zeta mass : ℝ) :
    rho*(mass+2*zeta*rho)-(mass*rho+zeta*rho^2)=zeta*rho^2 := by ring

theorem normalized_labels_do_not_fix_pair_coupling {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (h : ∑ i, p i=1) (k : ℝ) :
    ∑ i, ∑ j, p i*p j*k = k := by
  calc
    _ = (∑ i, p i)*(∑ j, p j)*k := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _; ring
    _ = k := by rw [h]; ring

theorem gradient_energy_of_constant {ι : Type*} [Fintype ι]
    (J : ι → ι → ℝ) (a : ℝ) :
    ∑ i, ∑ j, J i j*(a-a)^2 = 0 := by simp

-- Exact expansion of the existing depleted source branch, s=r-1/2.
theorem floor_velocity_identity (s : ℝ) :
    (2*(s+1/2)-1)*(3-2*(s+1/2))=4*s*(1-s) := by ring

theorem floor_current_squared_identity (s : ℝ) :
    (s+1/2)^2*(4*s*(1-s))=s+3*s^2-4*s^4 := by ring

theorem floor_internal_energy_identity (s : ℝ) :
    (s+1/2)/2+(2/3)*(1-(s+1/2))^3=1/3+s^2-(2/3)*s^3 := by ring

theorem floor_total_energy_identity (s : ℝ) :
    (s+1/2)*(4*s*(1-s))/2+(1/3+s^2-(2/3)*s^3)-1/3 =
      s+2*s^2-(8/3)*s^3 := by ring

theorem floor_pressure_identity (s : ℝ) :
    (s+1/2)*(4*s*(1-s))/2-(1/3+s^2-(2/3)*s^3)+1/3 =
      s-(4/3)*s^3 := by ring

theorem floor_sound_speed_at_zero :
    ((1-4*(0:ℝ)^2)/(1+4*0-8*0^2))=1 := by norm_num

theorem floor_sound_speed_limit :
    Filter.Tendsto (fun s : ℝ => (1-4*s^2)/(1+4*s-8*s^2))
      (nhds 0) (nhds 1) := by
  have h : ContinuousAt (fun s : ℝ => (1-4*s^2)/(1+4*s-8*s^2)) 0 := by
    fun_prop (disch := norm_num)
  simpa using h.tendsto

theorem massive_halo_sound_is_subunit (mass zeta rho : ℝ)
    (hm : 0 < mass) (hz : 0 ≤ zeta) (hr : 0 ≤ rho) :
    0 ≤ (2*zeta*rho)/(mass+2*zeta*rho) ∧
    (2*zeta*rho)/(mass+2*zeta*rho) < 1 := by
  have hp : 0 ≤ 2*zeta*rho := by positivity
  have hd : 0 < mass+2*zeta*rho := by linarith
  constructor
  · exact div_nonneg hp (le_of_lt hd)
  · apply (div_lt_one hd).mpr; linarith

-- Weighted symmetric nonnegative kernel, including a Nyström quadrature.
theorem weighted_schur {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (K : ι → ι → ℝ) (B : ℝ)
    (hw : ∀ i, 0≤w i) (hK : ∀ i j, 0≤K i j)
    (hs : ∀ i j, K i j=K j i)
    (hb : ∀ i, ∑ j, w j*K i j ≤ B) :
    ∑ i, ∑ j, w i*w j*K i j*x i*x j ≤ B*∑ i, w i*(x i)^2 := by
  have pair (i j : ι) :
      w i*w j*K i j*x i*x j ≤
      (w i*w j*K i j*(x i)^2+w i*w j*K i j*(x j)^2)/2 := by
    have hn : 0 ≤ w i*w j*K i j := mul_nonneg (mul_nonneg (hw i) (hw j)) (hK i j)
    have hh := mul_nonneg hn (sq_nonneg (x i-x j))
    nlinarith
  have eq1 : (∑ i, ∑ j, w i*w j*K i j*(x i)^2) =
      ∑ i, w i*(x i)^2*(∑ j, w j*K i j) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  have eq2 : (∑ i, ∑ j, w i*w j*K i j*(x j)^2) =
      ∑ i, w i*(x i)^2*(∑ j, w j*K i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]; ring
  calc
    _ ≤ ∑ i, ∑ j, (w i*w j*K i j*(x i)^2+w i*w j*K i j*(x j)^2)/2 := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact pair i j
    _ = (∑ i, w i*(x i)^2*(∑ j, w j*K i j)) := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [eq1, eq2]; ring
    _ ≤ ∑ i, w i*(x i)^2*B := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (hb i) (mul_nonneg (hw i) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem nonradial_row_bound (r R G pi : ℝ) (hG : 0≤G) (hp : 0≤pi) :
    (4*pi*G/3)*(r*R-3*r^2/4) ≤ 4*pi*G*R^2/9 := by
  have hn : 0≤4*pi*G/3 := by positivity
  have h : r*R-3*r^2/4 ≤ R^2/3 := by nlinarith [sq_nonneg (3*r-2*R)]
  have hm := mul_le_mul_of_nonneg_left h hn
  nlinarith

theorem energy_coercivity (energy normSq zeta B : ℝ)
    (h : energy≤B*normSq) :
    (zeta-B/2)*normSq ≤ zeta*normSq-energy/2 := by nlinarith

-- This numerical enclosure is conditional on a rigorous upper bound on pi.
-- The companion theorem below discharges that premise using mathlib.
theorem benchmark_coefficient_bound (R zeta pi : ℝ)
    (hr : 0≤R) (hR : R≤6223/1000) (hz : 45363/1000≤zeta)
    (hp : 0≤pi) (hpU : pi≤22/7) :
    2*pi*R^2 < (3/5)*9*zeta := by
  have hr2 : R^2 ≤ (6223/1000:ℝ)^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hr2 (show 0≤2*pi by positivity)
  have hc := mul_le_mul_of_nonneg_right hpU (show 0≤2*(6223/1000:ℝ)^2 by positivity)
  nlinarith

theorem benchmark_real_pi_bound (R zeta : ℝ)
    (hr : 0 ≤ R) (hR : R ≤ 6223/1000) (hz : 45363/1000 ≤ zeta) :
    2*Real.pi*R^2 < (3/5)*9*zeta := by
  apply benchmark_coefficient_bound R zeta Real.pi hr hR hz (le_of_lt Real.pi_pos)
  have hp := Real.pi_lt_d4
  linarith

-- Compact-baryon/deep-RAR matching fixes the coefficient, rather than tuning
-- it for stability. These algebraic statements assume that approximate family.
theorem matched_family_row_margin (a R eta G pi : ℝ)
    (ha : 0 ≤ a) (hR : 0 ≤ R) (hRa : R ≤ 2*a)
    (he : 0 ≤ eta) (hG : 0 ≤ G) (hp : 0 ≤ pi) :
    (2*pi*G*R^2)/9 ≤ (8/9)*(pi*G*(1+eta)*a^2) := by
  have hr2 : R^2 ≤ 4*a^2 := by nlinarith
  have hn : 0 ≤ pi*G := mul_nonneg hp hG
  have hh := mul_le_mul_of_nonneg_left hr2 hn
  have hE : 0 ≤ pi*G*eta*a^2 := by positivity
  nlinarith

theorem matched_family_energy_margin (energy normSq zeta : ℝ)
    (h : energy/2 ≤ (8/9)*zeta*normSq) :
    (1/9)*zeta*normSq ≤ zeta*normSq-energy/2 := by linarith

theorem matched_coefficient_from_rar_slope (A a G eta zeta : ℝ)
    (hA : A ≠ 0) (ha : a ≠ 0) (hp : Real.pi ≠ 0)
    (h : 2*zeta*(-A/(2*Real.pi*a^3)) = -G*A*(1+eta)/a) :
    zeta = Real.pi*G*(1+eta)*a^2 := by
  field_simp [ha, hp, hA] at h
  linarith

theorem edge_bound_from_arctangent_bound (a q : ℝ)
    (ha : 0 ≤ a) (hq : 0 < q) (hu : Real.arctan q ≤ q) :
    a*(1+Real.arctan q/q) ≤ 2*a := by
  have hdiv : Real.arctan q/q ≤ 1 := (div_le_one hq).mpr hu
  have hh := mul_le_mul_of_nonneg_left hdiv ha
  nlinarith

-- u=R/a, t=(R-a)/a. The continuum radial Poincare estimate has ratio
-- 2*u^2*t^2 / (pi^2*(1+eta)). This proves the dimensionless family bound.
theorem matched_family_radial_margin (u t eta pi : ℝ)
    (hu : 0 ≤ u) (hu2 : u ≤ 2) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he : 0 ≤ eta) (hp : 3 ≤ pi) :
    2*u^2*t^2 ≤ (8/9)*pi^2*(1+eta) := by
  have huSq : u^2 ≤ 4 := by nlinarith
  have htSq : t^2 ≤ 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left htSq (sq_nonneg u)
  have hpi : 9 ≤ pi^2 := by nlinarith
  have hE : 0 ≤ pi^2*eta := mul_nonneg (sq_nonneg _) he
  nlinarith

theorem combined_density_energy (radial angular nr na zeta c : ℝ)
    (hr : c*zeta*nr ≤ radial) (ha : c*zeta*na ≤ angular) :
    c*zeta*(nr+na) ≤ radial+angular := by nlinarith

end Entropic.MicroEnvelope3D
