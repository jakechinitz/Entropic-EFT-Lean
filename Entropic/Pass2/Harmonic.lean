import Entropic.Pass2.Fields

/-! Second pass, chunk 17: the weak maximum principle and the vanishing of harmonic functions that decay at
infinity on ℝⁿ (n ≥ 1): C11-56, C03-133, and with `Fields` the full C01-45 (Φ = Ψ). -/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Entropic.Var

variable {n : ℕ}

/-- Second-derivative test: at a local maximum of a C² function of one variable, g'' ≤ 0. -/
theorem second_deriv_nonpos {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hmax : IsLocalMax g 0) :
    deriv (deriv g) 0 ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  have hdg : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.1 hg).2.2
  have hd2 : Continuous (deriv (deriv g)) := hdg.continuous_deriv le_rfl
  have hd0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hd2.isOpen_preimage _ isOpen_Ioi |>.mem_nhds hpos)
  obtain ⟨s, hs, hsmax⟩ := Metric.mem_nhds_iff.1 hmax
  set t := min (r / 2) (s / 2) with ht
  have ht0 : 0 < t := lt_min (half_pos hr) (half_pos hs)
  have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  have hts : t < s := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hs)
  have hmono : StrictMonoOn (deriv g) (Icc 0 t) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 t) hdg.continuous.continuousOn fun y hy => ?_
    rw [interior_Icc] at hy
    exact hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hy.1]; exact hy.2.trans htr)
  have hgmono : StrictMonoOn g (Icc 0 t) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 t) hg.continuous.continuousOn fun y hy => ?_
    rw [interior_Icc] at hy
    have := hmono ⟨le_rfl, ht0.le⟩ ⟨hy.1.le, hy.2.le⟩ hy.1
    rwa [hd0] at this
  have h1 : g 0 < g t := hgmono ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩ ht0
  have h2 : g t ≤ g 0 := hsmax (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact hts)
  linarith

/-- At a local maximum p of a C² function, every ∂ᵢ∂ᵢ v(p) ≤ 0. -/
theorem pd_pd_nonpos {v : E n → ℝ} (hv : ContDiff ℝ 2 v) {p : E n} (hmax : IsLocalMax v p) (i : Fin n) :
    pd (pd v i) i p ≤ 0 := by
  set e := ev (n := n) i
  set g : ℝ → ℝ := fun t => v (p + t • e) with hgdef
  have hline : ContDiff ℝ 2 fun t : ℝ => p + t • e := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hg : ContDiff ℝ 2 g := hv.comp hline
  have hgmax : IsLocalMax g 0 := by
    have h0 : (fun t : ℝ => p + t • e) 0 = p := by simp
    have hm : IsLocalMax v ((fun t : ℝ => p + t • e) 0) := by rw [h0]; exact hmax
    exact IsLocalMax.comp_continuous (g := fun t : ℝ => p + t • e) (b := 0) hm hline.continuous.continuousAt
  have hdg : deriv g = fun t => pd v i (p + t • e) := by
    funext t
    have h1 : HasDerivAt (fun t : ℝ => p + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add p
    have h2 := ((diff_of_c1 (c1_of_c2 hv)) (p + t • e)).hasFDerivAt.comp_hasDerivAt t h1
    exact h2.deriv
  have hdd : deriv (deriv g) 0 = pd (pd v i) i p := by
    rw [hdg]
    have h1 : HasDerivAt (fun t : ℝ => p + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add p
    have h2 := ((diff_of_c1 (pd_c1 hv i)) (p + (0:ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
    have h3 := h2.deriv
    simp only [Function.comp_def] at h3
    rw [h3]; simp [pd, e]
  rw [← hdd]; exact second_deriv_nonpos hg hgmax

/-- At a local maximum, Δv ≤ 0. -/
theorem lap_nonpos_of_max {v : E n → ℝ} (hv : ContDiff ℝ 2 v) {p : E n} (hmax : IsLocalMax v p) :
    lap v p ≤ 0 := by
  unfold lap dvg; exact Finset.sum_nonpos fun i _ => pd_pd_nonpos hv hmax i

/-- The quadratic weight |x|². -/
noncomputable def nsq (x : E n) : ℝ := ‖x‖ ^ 2

theorem nsq_contDiff : ContDiff ℝ ⊤ (nsq (n := n)) := contDiff_norm_sq ℝ

theorem pd_nsq (i : Fin n) (x : E n) : pd nsq i x = 2 * x i := by
  have h : HasFDerivAt (nsq (n := n)) (2 • innerSL ℝ x) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [pd, h.fderiv]
  simp [ev, EuclideanSpace.inner_single_right]

theorem lap_nsq (x : E n) : lap nsq x = 2 * n := by
  have e : ∀ i, pd (nsq (n := n)) i = fun y => 2 * y i := fun i => funext (pd_nsq i)
  simp only [lap, dvg, e]
  have : ∀ i : Fin n, pd (fun y : E n => 2 * y i) i x = 2 := by
    intro i
    have hl : HasFDerivAt (fun y : E n => 2 * y i) ((2:ℝ) • (EuclideanSpace.proj i : E n →L[ℝ] ℝ)) x := by
      have := ((EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul (2:ℝ)
      simpa using this
    simp [pd, hl.fderiv, ev]
  simp [this, mul_comm]

theorem lap_add_smul_nsq {u : E n → ℝ} (hu : ContDiff ℝ 2 u) (δ : ℝ) (x : E n) :
    lap (fun y => u y + δ * nsq y) x = lap u x + δ * (2 * n) := by
  have hn : ContDiff ℝ 2 (nsq (n := n)) := nsq_contDiff.of_le le_top
  have e : ∀ i, pd (fun y => u y + δ * nsq y) i = fun y => pd u i y + δ * pd nsq i y := fun i =>
    funext fun y => by
      rw [pd_add (diff_of_c1 (c1_of_c2 hu)) ((diff_of_c1 (c1_of_c2 hn)).const_mul δ),
        pd_const_mul (diff_of_c1 (c1_of_c2 hn))]
  simp only [lap, dvg, e]
  rw [← lap_nsq x]
  simp only [lap, dvg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pd_add (diff_of_c1 (pd_c1 hu i)) ((diff_of_c1 (pd_c1 hn i)).const_mul δ),
    pd_const_mul (diff_of_c1 (pd_c1 hn i))]

/-- Weak maximum principle on a closed ball: a harmonic u bounded by M on the sphere |x| = R is bounded by M
on the ball. -/
theorem weak_max (hn : 0 < n) {u : E n → ℝ} (hu : ContDiff ℝ 2 u) (hΔ : ∀ x, lap u x = 0) {R M : ℝ}
    (hb : ∀ x : E n, ‖x‖ = R → u x ≤ M) {x : E n} (hx : ‖x‖ ≤ R) : u x ≤ M := by
  have hn2 : ContDiff ℝ 2 (nsq (n := n)) := nsq_contDiff.of_le le_top
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set δ := ε / (R ^ 2 + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  set v : E n → ℝ := fun y => u y + δ * nsq y with hv
  have hvc : ContDiff ℝ 2 v := hu.add (contDiff_const.mul hn2)
  obtain ⟨p, hp, hpmax⟩ := (isCompact_closedBall (0 : E n) R).exists_isMaxOn
    ⟨x, by simpa using hx⟩ hvc.continuous.continuousOn
  have hpR : ‖p‖ = R := by
    by_contra hne
    have hlt : ‖p‖ < R := lt_of_le_of_ne (by simpa using hp) hne
    have hloc : IsLocalMax v p := by
      apply hpmax.isLocalMax
      exact Metric.isOpen_ball.mem_nhds (by simpa using hlt) |> fun h =>
        Filter.mem_of_superset h Metric.ball_subset_closedBall
    have h1 := lap_nonpos_of_max hvc hloc
    rw [show lap v p = lap (fun y => u y + δ * nsq y) p from rfl, lap_add_smul_nsq hu, hΔ] at h1
    have : (0:ℝ) < δ * (2 * n) := mul_pos hδ0 (by positivity)
    linarith
  have hvx : v x ≤ v p := hpmax (by simpa using hx)
  have hux : u x ≤ v x := by simp only [hv, nsq]; nlinarith [sq_nonneg ‖x‖]
  have hvp : v p ≤ M + δ * R ^ 2 := by
    simp only [hv, nsq, hpR]; linarith [hb p hpR]
  have : δ * R ^ 2 < ε := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- C11-56, C03-133: a harmonic function on ℝⁿ (n ≥ 1) that tends to 0 at infinity vanishes identically. -/
theorem harmonic_decay_zero (hn : 0 < n) {u : E n → ℝ} (hu : ContDiff ℝ 2 u) (hΔ : ∀ x, lap u x = 0)
    (hlim : Tendsto u (cocompact (E n)) (𝓝 0)) : u = 0 := by
  have hneg : ContDiff ℝ 2 (fun y => -u y) := hu.neg
  have hΔneg : ∀ x, lap (fun y => -u y) x = 0 := fun x => by
    have := lap_sub (contDiff_const (c := (0:ℝ))) hu x
    simp only [zero_sub] at this
    rw [this, hΔ]; simp [lap, dvg, pd_const_fun, pd_const]
  funext x
  refine le_antisymm ?_ ?_ <;> refine le_of_forall_pos_le_add fun ε hε => ?_
  all_goals
    have hev : ∀ᶠ y in cocompact (E n), |u y| < ε := by
      have := hlim (Metric.ball_mem_nhds 0 hε)
      filter_upwards [this] with y hy
      simpa [Real.dist_eq] using hy
    obtain ⟨K, hK, hKs⟩ := (Filter.mem_cocompact.1 hev)
    obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall 0
    set R := max R0 ‖x‖ + 1
    have hout : ∀ y : E n, ‖y‖ = R → |u y| < ε := by
      intro y hy
      apply hKs
      intro hyK
      have := hR0 hyK
      rw [Metric.mem_closedBall, dist_zero_right] at this
      have : R ≤ R0 := hy ▸ this
      linarith [le_max_left R0 ‖x‖]
    have hxR : ‖x‖ ≤ R := by linarith [le_max_right R0 ‖x‖]
  · have := weak_max hn hu hΔ (M := ε) (fun y hy => (abs_lt.1 (hout y hy)).2.le) hxR
    simp; linarith
  · have := weak_max hn hneg hΔneg (M := ε) (fun y hy => by linarith [(abs_lt.1 (hout y hy)).1]) hxR
    simp at this ⊢; linarith

/-- C01-45 (second part), C11-56: if Δ(Φ − Ψ) = 0 and Φ − Ψ → 0 at infinity, then Φ = Ψ. -/
theorem no_slip (hn : 0 < n) {Φ Ψ : E n → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (hΔ : ∀ x, lap (fun y => Φ y - Ψ y) x = 0)
    (hlim : Tendsto (fun y => Φ y - Ψ y) (cocompact (E n)) (𝓝 0)) : Φ = Ψ := by
  have := harmonic_decay_zero hn (hΦ.sub hΨ) hΔ hlim
  funext x; exact sub_eq_zero.1 (congrFun this x)

/-- C01-45: for the two-potential action with C² fields, stationarity under independent test variations of
Φ and Ψ, together with Φ − Ψ → 0 at infinity, gives ΔΨ = 4πGρ and Φ = Ψ; then I^(2)[Φ, Φ] = I_Newton[Φ]. -/
theorem two_potential_newton (hn : 0 < n) {G : ℝ} (hG : G ≠ 0) {ρ Φ Ψ : E n → ℝ} (hρ : Continuous ρ)
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ)
    (h1 : ∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ f Ψ) Φ η) 0 0)
    (h2 : ∀ η, IsTest η → HasDerivAt (var (fun f => I2 G ρ Φ f) Ψ η) 0 0)
    (hlim : Tendsto (fun y => Φ y - Ψ y) (cocompact (E n)) (𝓝 0)) :
    (∀ x, lap Ψ x = 4 * Real.pi * G * ρ x) ∧ Φ = Ψ ∧ ∀ x, I2 G ρ Φ Ψ x = IN G ρ Φ x := by
  have e1 := (two_potential_Φ hG hρ hΦ hΨ).1 h1
  have e2 := (two_potential_Ψ hG hρ hΦ hΨ).1 h2
  have hEq := no_slip hn hΦ hΨ e2 hlim
  refine ⟨e1, hEq, fun x => ?_⟩
  rw [← I2_diag, ← hEq]

end Entropic.Var
