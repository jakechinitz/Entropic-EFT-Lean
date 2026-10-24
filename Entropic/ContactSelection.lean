import Mathlib

/-!
# Contact selection: Bose-cell statistics, orbit populations, and stock contacts

Local contract. The response cell of Section 15 has gap `Θ x`, `x = sqrt(g_b/a0)`, and mean
occupation `n* = 1/(e^x - 1)`. This module proves the statistical and mechanical identities
that a stock-contact selection rule rests on. It does not derive a microscopic exchange
operator, a relaxation rate, a cluster gate or halo formation.

Section 1 (from the "Constitutive contact bridge" research note, ported to Lean 4.35):
the Bose entropy and gap function, the affinity, dissipative sign, fixed-basis orbit pairing,
exact quadratic variation, finite-step descent bound, central-impulse energetics, heat/work
bookkeeping and two-pole monotonicity.

Section 2 (new):
* `boseGap_eq_relEnt`, `relEnt_nonneg`, `boseGap_nonneg`: the gap function is the relative
  entropy of geometric distributions with means `n` and `n*`, hence nonnegative, and it
  vanishes at `n = n*`;
* `boseGap_second_derivative`: its curvature `1/(n(1+n))`, the inverse occupation variance;
* `equipartition_matching`: the quadratic field mismatch `(δg)^2/(8πG)` is the Gaussian
  limit of `𝒩 Θ D` exactly when `𝒩 Θ = g_b^2 n(1+n)/(4πG)`;
* `uphill_rate_vanishes`: local detailed balance at bath temperature `Θ → 0⁺` suppresses
  every transition that raises the free energy;
* `symmetric_flow_dissipates`: a symmetric nonnegative mobility on orbit populations
  never raises the functional (finite H-theorem);
* `pair_impulse_conserves_angular_momentum`: an equal and opposite impulse along the pair
  separation conserves total momentum and angular momentum;
* `stiff_coupling_amplification`: a stiff penalty coupling transmits a stock Jeans
  imbalance `d` to the baryons as `-d g_R (1 + λ J')/(λ - 1)`;
* `vp_acceleration_scaling`: the Vlasov-Poisson scaling moves accelerations by `β²/α`;
* `clip_renormalise_not_minimal`: the three-shell counterexample to clip-and-renormalise.

Section 3 (galaxy and cluster bookkeeping): the occupation is the enclosed stock-to-baryon
ratio; clipping a monotone target at the budget is the optimal admissible profile; the
weak-lensing stock bound `S ≥ (π/4) sqrt(a0/g) - 1`; an always-on field response misses the
X-COP cluster ratios while the cohort value `1 + k_C` lies between them; no cells means no
bias; the precision needed for the `a0(z)` ratio test.
-/

noncomputable section
open scoped BigOperators Matrix
open Filter Topology

namespace Entropic.ContactSelection

/-! ## 1. Bose cell and contact bookkeeping -/

/-- Entropy of a geometric (Bose) occupation distribution with mean `n`. -/
def boseEntropy (n : ℝ) : ℝ := (1+n)*Real.log (1+n) - n*Real.log n

/-- Excess free energy, in units of `Θ`, of mean occupation `n` at gap `x`. -/
def boseGap (n x : ℝ) : ℝ := x*n - boseEntropy n - Real.log (1 - Real.exp (-x))

theorem bose_entropy_derivative (n : ℝ) (hn : 0 < n) :
    HasDerivAt boseEntropy (Real.log (1+n) - Real.log n) n := by
  have hp : 0 < 1+n := by linarith
  have h1 : HasDerivAt (fun t : ℝ => 1+t) 1 n := by
    simpa using (hasDerivAt_id n).const_add 1
  have ha := h1.mul (h1.log hp.ne')
  have hb := (hasDerivAt_id n).mul ((hasDerivAt_id n).log hn.ne')
  have h := ha.sub hb
  convert h using 1
  · funext t; simp [boseEntropy]
  · simp [hn.ne', hp.ne']

theorem bose_gap_derivative (n x : ℝ) (hn : 0 < n) :
    HasDerivAt (fun t => boseGap t x) (x - (Real.log (1+n) - Real.log n)) n := by
  have h := (((hasDerivAt_id n).const_mul x).sub (bose_entropy_derivative n hn)).sub_const
    (Real.log (1 - Real.exp (-x)))
  convert h using 1
  · funext t; simp [boseGap]
  · simp

theorem log_affinity_identity (n : ℝ) (hn : 0 < n) :
    Real.log (1+n) - Real.log n = Real.log (1+1/n) := by
  rw [← Real.log_div (by linarith : (1:ℝ)+n ≠ 0) hn.ne']
  congr 1
  field_simp
  ring

theorem occupation_free_energy_dissipates (n target gamma : ℝ)
    (hn : 0 < n) (ht : 0 < target) (hg : 0 ≤ gamma) :
    (Real.log (1+1/target) - Real.log (1+1/n))*(gamma*(target-n)) ≤ 0 := by
  rcases le_total n target with h | h
  · have hi : (1:ℝ)/target ≤ 1/n := one_div_le_one_div_of_le hn h
    have hl : Real.log (1+1/target) ≤ Real.log (1+1/n) := by
      apply Real.log_le_log (by positivity); linarith
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl)
      (mul_nonneg hg (sub_nonneg.mpr h))
  · have hi : (1:ℝ)/n ≤ 1/target := one_div_le_one_div_of_le ht h
    have hl : Real.log (1+1/n) ≤ Real.log (1+1/target) := by
      apply Real.log_le_log (by positivity); linarith
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl)
      (mul_nonpos_of_nonneg_of_nonpos hg (sub_nonpos.mpr h))

/-- For a fixed orbit-density basis, the orbit average of the functional derivative is
the derivative with respect to that orbit's weight. -/
theorem orbit_pairing {I X : Type*} [Fintype I] [Fintype X]
    (dw : I → ℝ) (density : I → X → ℝ) (psi volume : X → ℝ) :
    (∑ x, volume x*psi x*(∑ i, dw i*density i x)) =
      ∑ i, dw i*(∑ x, volume x*psi x*density i x) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro x _
  ring

theorem exact_field_variation {X : Type*} [Fintype X] (p J dp weight : X → ℝ) :
    (∑ x, weight x*((p x+dp x-J x)^2-(p x-J x)^2)) =
      (∑ x, 2*weight x*(p x-J x)*dp x) + (∑ x, weight x*(dp x)^2) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  ring

theorem finite_descent_with_curvature (slope curvature step : ℝ)
    (_hs : slope ≤ 0) (hc : 0 < curvature) (ht : 0 ≤ step)
    (hb : step ≤ -2*slope/curvature) :
    slope*step + curvature*step^2/2 ≤ 0 := by
  have h : step*curvature ≤ -2*slope := (le_div_iff₀ hc).mp hb
  have hh := mul_le_mul_of_nonneg_right h ht
  nlinarith

theorem negative_first_variation_can_increase :
    (-1:ℝ)*3 < 0 ∧ 0 < (-1:ℝ)*3 + 1*3^2/2 := by norm_num

theorem positional_cost_cancels (Ki Kj V A theta : ℝ) :
    -((Kj+V+A)-(Ki+V+A))/theta = -(Kj-Ki)/theta := by ring

theorem central_energy_completion (mu u q : ℝ) (hm : 0 < mu) :
    q*u + q^2/(2*mu) + mu*u^2/2 = (q+mu*u)^2/(2*mu) := by
  field_simp; ring

theorem central_cooling_bound (mu u q : ℝ) (hm : 0 < mu) :
    -mu*u^2/2 ≤ q*u + q^2/(2*mu) := by
  have h := central_energy_completion mu u q hm
  have hp : 0 ≤ (q+mu*u)^2/(2*mu) := by positivity
  linarith

theorem driven_descent_has_heat_cost (deltaE deltaD theta lambda : ℝ)
    (hd : deltaD < 0) (ht : 0 < theta) (hl : 0 < lambda) :
    deltaE < deltaE - theta*lambda*deltaD := by
  have h : theta*lambda*deltaD < 0 := mul_neg_of_pos_of_neg (mul_pos ht hl) hd
  linarith

theorem two_pole_denominator_monotone (gamma Omega a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (gamma^2+a)*(Omega^2+a) ≤ (gamma^2+b)*(Omega^2+b) := by
  have h1 : 0 ≤ (b-a)*gamma^2 := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)
  have h2 : 0 ≤ (b-a)*Omega^2 := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _)
  have h3 : 0 ≤ (b-a)*(b+a) := mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  nlinarith

/-! ## 2. Relative entropy, matching, detailed balance and conservation -/

/-- Relative entropy of the geometric distribution with mean `n` from the one with mean `m`. -/
def relEnt (n m : ℝ) : ℝ := n*Real.log (n/m) - (1+n)*Real.log ((1+n)/(1+m))

/-- The Bose mean occupation at gap `x`. -/
def nStar (x : ℝ) : ℝ := 1/(Real.exp x - 1)

theorem boseGap_eq_relEnt (n x : ℝ) (hn : 0 < n) (hx : 0 < x) :
    boseGap n x = relEnt n (nStar x) := by
  have he : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hd : 0 < Real.exp x - 1 := by linarith
  have hm : 0 < nStar x := by unfold nStar; positivity
  have h1m : 1 + nStar x = Real.exp x/(Real.exp x - 1) := by
    unfold nStar; field_simp; ring
  have hlog1m : Real.log (1 + nStar x) = x - Real.log (Real.exp x - 1) := by
    rw [h1m, Real.log_div (Real.exp_pos x).ne' hd.ne', Real.log_exp]
  have hlogm : Real.log (nStar x) = -Real.log (Real.exp x - 1) := by
    unfold nStar; rw [one_div, Real.log_inv]
  have hexp : 1 - Real.exp (-x) = (Real.exp x - 1)/Real.exp x := by
    rw [Real.exp_neg]; field_simp
  have hlogexp : Real.log (1 - Real.exp (-x)) = Real.log (Real.exp x - 1) - x := by
    rw [hexp, Real.log_div hd.ne' (Real.exp_pos x).ne', Real.log_exp]
  have hn1 : (0:ℝ) < 1 + n := by linarith
  unfold boseGap boseEntropy relEnt
  rw [Real.log_div hn.ne' hm.ne', Real.log_div hn1.ne' (by linarith : (1:ℝ) + nStar x ≠ 0),
    hlog1m, hlogm, hlogexp]
  ring

/-- Relative entropy of geometric distributions is nonnegative (convexity of `t log t`). -/
theorem relEnt_nonneg (n m : ℝ) (hn : 0 ≤ n) (hm : 0 < m) : 0 ≤ relEnt n m := by
  have hm1 : 0 < 1 + m := by linarith
  set a := n/m with ha
  set b := (1+n)/(1+m) with hb
  have hw1 : 0 ≤ 1/(1+m) := by positivity
  have hw2 : 0 ≤ m/(1+m) := by positivity
  have hsum : 1/(1+m) + m/(1+m) = 1 := by field_simp
  have hcomb : (1/(1+m)) • (1:ℝ) + (m/(1+m)) • a = b := by
    simp only [smul_eq_mul, ha, hb]; field_simp
  have hconv := Real.convexOn_mul_log.2 (Set.mem_Ici.mpr zero_le_one)
    (Set.mem_Ici.mpr (by positivity : (0:ℝ) ≤ a)) hw1 hw2 hsum
  rw [hcomb] at hconv
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconv
  -- (1+m) φ(b) ≤ m φ(a)
  have key : (1+m)*(b*Real.log b) ≤ m*(a*Real.log a) := by
    have := mul_le_mul_of_nonneg_left hconv hm1.le
    calc (1+m)*(b*Real.log b) ≤ (1+m)*(m/(1+m)*(a*Real.log a)) := this
      _ = m*(a*Real.log a) := by field_simp
  have e1 : m*(a*Real.log a) = n*Real.log (n/m) := by
    simp only [ha]; field_simp
  have e2 : (1+m)*(b*Real.log b) = (1+n)*Real.log ((1+n)/(1+m)) := by
    simp only [hb]; field_simp
  unfold relEnt
  linarith

theorem relEnt_self (m : ℝ) (hm : 0 < m) : relEnt m m = 0 := by
  unfold relEnt
  rw [div_self hm.ne', div_self (by linarith : (1:ℝ)+m ≠ 0), Real.log_one]; ring

/-- The Bose excess free energy is nonnegative and vanishes at the native occupation. -/
theorem boseGap_nonneg (n x : ℝ) (hn : 0 < n) (hx : 0 < x) : 0 ≤ boseGap n x := by
  rw [boseGap_eq_relEnt n x hn hx]
  exact relEnt_nonneg n _ hn.le (by unfold nStar; have := Real.one_lt_exp_iff.mpr hx; positivity)

theorem boseGap_at_nStar (x : ℝ) (hx : 0 < x) : boseGap (nStar x) x = 0 := by
  have hm : 0 < nStar x := by
    unfold nStar; have := Real.one_lt_exp_iff.mpr hx; have : 0 < Real.exp x - 1 := by linarith
    positivity
  rw [boseGap_eq_relEnt _ x hm hx, relEnt_self _ hm]

/-- The curvature of the excess free energy is the inverse occupation variance `n(1+n)`. -/
theorem boseGap_second_derivative (n x : ℝ) (hn : 0 < n) :
    HasDerivAt (fun t => x - (Real.log (1+t) - Real.log t)) (1/(n*(1+n))) n := by
  have hp : 0 < 1+n := by linarith
  have h1 : HasDerivAt (fun t : ℝ => 1+t) 1 n := by simpa using (hasDerivAt_id n).const_add 1
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (1+t)) (1/(1+n)) n := h1.log hp.ne'
  have hlog2 : HasDerivAt Real.log n⁻¹ n := Real.hasDerivAt_log hn.ne'
  have h := (hlog1.sub hlog2).const_sub x
  convert h using 1
  field_simp
  ring

/-- Gaussian matching: the quadratic field mismatch with coefficient `1/(4πG)` (that is,
`(δg)^2/(8πG)`) is the second-order term of `𝒩 Θ D(n‖n*)` with `δn = δg/g_b`, exactly when
the cell free-energy density obeys the equipartition condition below. -/
theorem equipartition_matching (cellFE g n G : ℝ) (hg : g ≠ 0) (hn : 0 < n) (hG : 0 < G) :
    cellFE/(g^2*(n*(1+n))) = 1/(4*Real.pi*G) ↔
      cellFE = g^2*(n*(1+n))/(4*Real.pi*G) := by
  have h1 : 0 < g^2*(n*(1+n)) := by positivity
  have h2 : 0 < 4*Real.pi*G := by positivity
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; rw [h]; field_simp

/-- Local detailed balance at bath temperature `θ`: the uphill rate ratio `exp(-ΔF/θ)`
vanishes as `θ → 0⁺` for every free-energy increase `ΔF > 0`. -/
theorem uphill_rate_vanishes (dF : ℝ) (hdF : 0 < dF) :
    Tendsto (fun θ : ℝ => Real.exp (-(dF/θ))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun θ : ℝ => θ⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun θ : ℝ => dF/θ) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using h1.const_mul_atTop hdF
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h2

/-- Finite H-theorem: with a symmetric mobility, the rate of change of the functional along
`ẇ_i = Σ_j L_ij (μ_j - μ_i)` is `-(1/2) Σ L_ij (μ_i - μ_j)^2`. -/
theorem symmetric_flow_identity {I : Type*} [Fintype I] (L : I → I → ℝ) (mu : I → ℝ)
    (hL : ∀ i j, L i j = L j i) :
    (∑ i, (∑ j, L i j*(mu j - mu i))*mu i) =
      -(1/2)*∑ i, ∑ j, L i j*(mu i - mu j)^2 := by
  have hswap : (∑ i, ∑ j, L i j*(mu j - mu i)*mu i) =
      ∑ i, ∑ j, L i j*(mu i - mu j)*mu j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hL j i]
  have hsplit : (∑ i, (∑ j, L i j*(mu j - mu i))*mu i) =
      ∑ i, ∑ j, L i j*(mu j - mu i)*mu i := by
    apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
  have hsq : (∑ i, ∑ j, L i j*(mu i - mu j)^2) =
      -((∑ i, ∑ j, L i j*(mu j - mu i)*mu i) + ∑ i, ∑ j, L i j*(mu i - mu j)*mu j) := by
    rw [← neg_neg (∑ i, ∑ j, L i j*(mu i - mu j)^2), ← Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hsplit, hsq, hswap]; ring

theorem symmetric_flow_dissipates {I : Type*} [Fintype I] (L : I → I → ℝ) (mu : I → ℝ)
    (hL : ∀ i j, L i j = L j i) (hpos : ∀ i j, 0 ≤ L i j) :
    (∑ i, (∑ j, L i j*(mu j - mu i))*mu i) ≤ 0 := by
  rw [symmetric_flow_identity L mu hL]
  have : 0 ≤ ∑ i, ∑ j, L i j*(mu i - mu j)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hpos i j) (sq_nonneg _)
  linarith

/-- An equal and opposite impulse along the pair separation conserves total momentum and
total angular momentum. -/
theorem pair_impulse_conserves_momentum (p : Fin 3 → ℝ) : p + (-p) = 0 := by simp

theorem pair_impulse_conserves_angular_momentum (xi xj : Fin 3 → ℝ) (s : ℝ) :
    xi ⨯₃ (s • (xi - xj)) + xj ⨯₃ (-(s • (xi - xj))) = 0 := by
  have h : xi ⨯₃ (s • (xi - xj)) + xj ⨯₃ (-(s • (xi - xj))) =
      s • ((xi - xj) ⨯₃ (xi - xj)) := by
    simp only [map_neg, map_smul, map_sub, LinearMap.sub_apply]
    module
  rw [h, cross_self, smul_zero]

/-- Stiff-coupling amplification (exact algebra of the linearised spherical problem). If
stock force balance gives `(λ - 1)(J - g_s) = d g_R` with `g_R = g_b + J`, the baryon
acceleration `g_b + g_s + λ (g_s - J) J'` differs from `g_R` by
`-d g_R (1 + λ J')/(λ - 1)`. -/
theorem stiff_coupling_amplification (gb gs J Jp d lam : ℝ) (hl : lam ≠ 1)
    (h : (lam - 1)*(J - gs) = d*(gb + J)) :
    gb + gs + lam*(gs - J)*Jp - (gb + J) = -(d*(gb + J))*(1 + lam*Jp)/(lam - 1) := by
  have hl' : lam - 1 ≠ 0 := sub_ne_zero.mpr hl
  have hgs : gs - J = -(d*(gb + J))/(lam - 1) := by
    field_simp; linarith
  have : gb + gs + lam*(gs - J)*Jp - (gb + J) = (gs - J)*(1 + lam*Jp) := by ring
  rw [this, hgs]; ring

/-- Vlasov-Poisson scaling `x → αx`, `v → βv`, `M → αβ²M`: accelerations scale by `β²/α`,
so the dynamics carries no fixed acceleration scale. -/
theorem vp_acceleration_scaling (G M r α β : ℝ) (hα : α ≠ 0) (hr : r ≠ 0) :
    G*(α*β^2*M)/(α*r)^2 = (β^2/α)*(G*M/r^2) := by
  field_simp

/-- Three-shell counterexample: with target enclosed masses `(2,1,2)` and equal weights,
the clipped-and-renormalised profile `(4/3, 0, 2/3)` has mismatch `5/9`, while the
isotonic profile `(3/2, 0, 1/2)` has `1/2`. -/
theorem clip_renormalise_not_minimal :
    ((3/2:ℝ) - 2)^2 + ((3/2:ℝ) - 1)^2 < ((4/3:ℝ) - 2)^2 + ((4/3:ℝ) - 1)^2 := by norm_num

/-! ## 3. Galaxy and cluster bookkeeping -/

/-- Spherically, the occupation `n = g_s/g_b` is the enclosed stock-to-baryon mass ratio. -/
theorem occupation_is_enclosed_ratio (G Ms Mb r : ℝ) (hG : G ≠ 0) (hr : r ≠ 0) :
    (G*Ms/r^2)/(G*Mb/r^2) = Ms/Mb := by
  rcases eq_or_ne Mb 0 with h | h
  · simp [h]
  · field_simp

/-- Pointwise optimality of clipping: for any profile bounded by the budget `M`, the clipped
target `min T M` has no larger weighted mismatch. -/
theorem clip_optimal {K : Type*} [Fintype K] (T Y w : K → ℝ) (M : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hY : ∀ k, Y k ≤ M) :
    (∑ k, w k*(min (T k) M - T k)^2) ≤ ∑ k, w k*(Y k - T k)^2 := by
  apply Finset.sum_le_sum; intro k _
  apply mul_le_mul_of_nonneg_left _ (hw k)
  rcases le_total (T k) M with h | h
  · rw [min_eq_left h, sub_self]; nlinarith [sq_nonneg (Y k - T k)]
  · rw [min_eq_right h]
    have h1 : Y k - T k ≤ M - T k := by linarith [hY k]
    have h2 : M - T k ≤ 0 := by linarith
    nlinarith

/-- A non-decreasing target stays non-decreasing after clipping, so the clipped target is
an admissible (positive-density) stock profile and, by `clip_optimal`, the minimiser. -/
theorem clip_monotone {T : ℝ → ℝ} (hT : Monotone T) (M : ℝ) :
    Monotone (fun r => min (T r) M) := fun _ _ hab => min_le_min_right M (hT hab)

/-- Weak-lensing stock bound. An isolated finite halo has `ΔΣ ≤ (1+S) g/(πG)`; a deep-RAR
signal `ΔΣ = sqrt(g a0)/(4G)` therefore needs `S ≥ (π/4) sqrt(a0/g) - 1`. -/
theorem lensing_stock_bound (G g a0 S : ℝ) (hG : 0 < G) (hg : 0 < g) (ha : 0 < a0)
    (h : Real.sqrt (g*a0)/(4*G) ≤ (1+S)*g/(Real.pi*G)) :
    Real.pi/4*Real.sqrt (a0/g) - 1 ≤ S := by
  have hpi := Real.pi_pos
  have hsq : Real.sqrt (g*a0) = g*Real.sqrt (a0/g) := by
    rw [show g*a0 = g^2*(a0/g) by field_simp, Real.sqrt_mul (sq_nonneg g),
      Real.sqrt_sq hg.le]
  rw [hsq] at h
  have h' : g*Real.sqrt (a0/g)*(Real.pi*G) ≤ (1+S)*g*(4*G) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h; linarith
  have h'' : Real.sqrt (a0/g)*Real.pi ≤ (1+S)*4 := by
    have := (mul_le_mul_iff_of_pos_right (show 0 < g*G by positivity)).mp
      (by nlinarith [h'] : Real.sqrt (a0/g)*Real.pi*(g*G) ≤ (1+S)*4*(g*G))
    exact this
  linarith

/-- With the cohort stock retained, an RAR field response that stays on in clusters adds
its boost `B = 4.2-5.0` at `R500` to `k_C`, overshooting the X-COP median `6.45` by more
than 1.4; the RAR alone (`B ≤ 5.0`) falls short of it by at least 1.29. -/
theorem field_response_misses_clusters :
    1.4 < ((5.1760752:ℝ) + 4.2)/6.45 ∧ (6.45:ℝ)/5.0 ≥ 1.29 := by norm_num

/-- The cohort ratio `1 + k_C = 6.18` lies between the X-COP medians at `R200` and `R500`. -/
theorem cohort_between_xcop : (6.10:ℝ) < 1 + 5.1760752 ∧ 1 + (5.1760752:ℝ) < 6.45 := by
  norm_num

/-- Off active carriers the cell density vanishes, so the bias density
`𝒩 Θ ∂_n D` vanishes and the stock is collisionless there. -/
theorem no_cells_no_bias (cellFE affinity : ℝ) (h : cellFE = 0) : cellFE*affinity = 0 := by
  rw [h, zero_mul]

/-- Redshift test: separating `H(2.3)/H0 = 3.4648` from an alternative ratio `3.0` at three
standard deviations works with a 4.4% fractional uncertainty and fails at 4.5%. -/
theorem redshift_ratio_precision :
    3*(0.044*(3.4648:ℝ)) < 3.4648 - 3 ∧ 3.4648 - 3 < 3*(0.045*(3.4648:ℝ)) := by norm_num

end Entropic.ContactSelection
