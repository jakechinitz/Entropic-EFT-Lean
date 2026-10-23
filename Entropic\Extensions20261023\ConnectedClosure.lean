import Mathlib

/-! Standalone effective-closure certificates, checked with Lean/mathlib 4.19.
Physical selection of these effective actions is not asserted. Algebraic
principal-symbol checks are not a nonlinear spacetime existence theorem.
The integrating-factor proof follows Entropic.AppO.Release.linear_positivity.
-/
noncomputable section
open scoped BigOperators
namespace ConnectedClosure

def kineticX (r : ℝ) : ℝ := 1/2 - 2*(1-r)^2
def energyShape (r : ℝ) : ℝ := r/2 + (2/3)*(1-r)^3
def sourceFactor (r : ℝ) : ℝ := -1+6*r^2-4*r^3
def rateRatio (r : ℝ) : ℝ := (1+2*r-2*r^2)/(3-2*r)

theorem boundary_matching :
    energyShape 1 = 1/2 ∧ kineticX 1 = 1/2 ∧
    energyShape (1/2) = 1/3 ∧ kineticX (1/2) = 0 := by
  norm_num [energyShape, kineticX]

theorem energy_floor_factor (r : ℝ) :
    energyShape r - 1/3 = (2-r)*(2*r-1)^2/6 := by
  unfold energyShape; ring

theorem energy_floor {r : ℝ} (hr : r ≤ 1) : 1/3 ≤ energyShape r := by
  have h2 : 0 ≤ 2-r := by linarith
  have hp : 0 ≤ (2-r)*(2*r-1)^2/6 := by positivity
  rw [← energy_floor_factor] at hp
  linarith

theorem kinetic_nonnegative {r : ℝ} (h0 : 1/2 ≤ r) (h1 : r ≤ 1) :
    0 ≤ kineticX r := by
  have h : 0 ≤ (2*r-1)*(3-2*r) := mul_nonneg (by linarith) (by linarith)
  unfold kineticX; nlinarith

theorem kinetic_upper {r : ℝ} : kineticX r ≤ 1/2 := by
  unfold kineticX; nlinarith [sq_nonneg (1-r)]

theorem observer_energy_identity (lam e V t2 s2 : ℝ) :
    lam*t2 - (lam*((t2-s2)/2)-e-V) = lam*(t2+s2)/2+e+V := by ring

theorem observer_energy_positive (lam e V t2 s2 : ℝ)
    (hl : 0 ≤ lam) (he : 0 ≤ e) (hV : 0 ≤ V) (ht : 0 ≤ t2) (hs : 0 ≤ s2) :
    0 ≤ lam*(t2+s2)/2+e+V := by positivity

theorem adaptive_floor (L V K r : ℝ) (hL : 0 ≤ L)
    (hK : L=3*(K-V)) (hr : r ≤ 1) :
    K ≤ L*energyShape r+V := by
  have h := mul_le_mul_of_nonneg_left (energy_floor hr) hL
  nlinarith

theorem source_factorization (r : ℝ) :
    sourceFactor r = (2*r-1)*(1+2*r-2*r^2) := by
  unfold sourceFactor; ring

theorem source_bounds {r : ℝ} (h0 : 1/2 ≤ r) (h1 : r ≤ 1) :
    0 ≤ sourceFactor r ∧ sourceFactor r ≤ 1 := by
  have hprod : 0 ≤ r*(1-r) := mul_nonneg (by linarith) (by linarith)
  have hp : 0 ≤ (2*r-1)*(1+2*r-2*r^2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hq : 0 ≤ 2*(1-r)^2*(2*r+1) := by positivity
  rw [← source_factorization] at hp
  refine ⟨hp, ?_⟩
  unfold sourceFactor; nlinarith

theorem source_as_fractional_rate {r : ℝ} (h : 3-2*r ≠ 0) :
    sourceFactor r = rateRatio r * (2*kineticX r) := by
  unfold sourceFactor rateRatio kineticX
  field_simp; ring

theorem rate_ratio_bounds {r : ℝ} (h0 : 1/2 ≤ r) (h1 : r ≤ 1) :
    3/4 ≤ rateRatio r ∧ rateRatio r ≤ 1 := by
  have hd : 0 < 3-2*r := by linarith
  have hp : 0 ≤ (2*r-1)*(5-4*r) := mul_nonneg (by linarith) (by linarith)
  unfold rateRatio
  constructor
  · rw [le_div_iff₀ hd]; nlinarith
  · rw [div_le_iff₀ hd]; nlinarith [sq_nonneg (1-r)]

theorem empty_source : sourceFactor (1/2) = 0 := by norm_num [sourceFactor]

theorem dust_source : sourceFactor 1 = 1 := by norm_num [sourceFactor]

theorem current_factorization (J lam theta Vp A : ℝ) (hl : lam ≠ 0) :
    -theta*J-Vp*A*(J/lam)^2 = -(theta+Vp*A*J/lam^2)*J := by
  field_simp; ring

theorem sound_speed_range {r : ℝ} (h0 : 1/2 ≤ r) (h1 : r ≤ 1) :
    0 ≤ (4*r*(1-r))/(4*r*(1-r)+2*kineticX r) ∧
    (4*r*(1-r))/(4*r*(1-r)+2*kineticX r) ≤ 1 := by
  have hn : 0 ≤ 4*r*(1-r) := mul_nonneg (by linarith) (by linarith)
  have hx := kinetic_nonnegative h0 h1
  have hd : 0 < 4*r*(1-r)+2*kineticX r := by
    by_cases hr : r=1
    · subst r; norm_num [kineticX]
    · have hlt : r < 1 := (lt_iff_le_and_ne).2 ⟨h1, hr⟩
      have hh : 0 < 4*r*(1-r) := mul_pos (by linarith) (by linarith)
      linarith
  exact ⟨div_nonneg hn hd.le, (div_le_one hd).mpr (by linarith)⟩

theorem shape_hasDerivAt (r : ℝ) :
    HasDerivAt energyShape (kineticX r) r := by
  convert ((hasDerivAt_id r).div_const 2).add
    ((((hasDerivAt_id r).const_sub 1).pow 3).const_mul (2/3)) using 1 <;>
    simp [energyShape, kineticX] <;> ring

theorem kinetic_hasDerivAt (r : ℝ) :
    HasDerivAt kineticX (4*(1-r)) r := by
  convert ((((hasDerivAt_id r).const_sub 1).pow 2).const_mul 2).const_sub (1/2) using 1 <;>
    simp [kineticX] <;> ring

theorem unchanged_action (lam X V h : ℝ) (hh : h=0) :
    lam*X-lam/2-h-V = lam*(X-1/2)-V := by rw [hh]; ring

/-- Nonnegative solutions for regular rates; no division by the current. -/
theorem regular_rate_positivity (f K k s : ℝ → ℝ) (t0 : ℝ)
    (hf : ∀ t, HasDerivAt f (-k t*f t+s t) t)
    (hK : ∀ t, HasDerivAt K (k t) t)
    (hs : ∀ t, t0 ≤ t → 0 ≤ s t) (h0 : 0 ≤ f t0) :
    ∀ t, t0 ≤ t → 0 ≤ f t := by
  set g : ℝ → ℝ := fun t => f t*Real.exp (K t)
  have hg : ∀ t, HasDerivAt g (s t*Real.exp (K t)) t := by
    intro t
    convert (hf t).mul ((hK t).exp) using 1 <;> ring
  have hm : MonotoneOn g (Set.Ici t0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t0)
    · exact fun t _ => (hg t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hg t).deriv]
      exact mul_nonneg (hs t ht.le) (Real.exp_pos _).le
  intro t ht
  have h := hm (Set.mem_Ici.mpr le_rfl) ht ht
  have hbase : 0 ≤ g t0 := mul_nonneg h0 (Real.exp_pos _).le
  have hgt : 0 ≤ g t := le_trans hbase h
  exact nonneg_of_mul_nonneg_left hgt (Real.exp_pos (K t))

theorem passive_lag_sign (n q qd gamma K : ℝ → ℝ) (t0 : ℝ)
    (hn : ∀ t, HasDerivAt n (gamma t*(q t-n t)) t)
    (hq : ∀ t, HasDerivAt q (qd t) t)
    (hK : ∀ t, HasDerivAt K (gamma t) t)
    (hfall : ∀ t, t0 ≤ t → qd t ≤ 0) (h0 : q t0 ≤ n t0) :
    ∀ t, t0 ≤ t → q t ≤ n t := by
  have h := regular_rate_positivity (fun t => n t-q t) K gamma (fun t => -qd t) t0
    (fun t => by convert (hn t).sub (hq t) using 1 <;> ring) hK
    (fun t ht => neg_nonneg.mpr (hfall t ht)) (by change 0 ≤ n t0-q t0; linarith)
  intro t ht; have hh := h t ht; dsimp at hh; linarith

theorem finite_positive_memory {ι : Type*} [Fintype ι]
    (w q : ι → ℝ) (now : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i=1) (hq : ∀ i, now ≤ q i) :
    now ≤ ∑ i, w i*q i := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hq i) (hw i))
  simpa [← Finset.sum_mul, hs] using h

theorem rate_scaling (a b p q k : ℝ) (h : a*p=b*q) :
    (k*a)*p=(k*b)*q := by nlinarith [congrArg (fun z : ℝ => k*z) h]

def logGap (r : ℝ) : ℝ := Real.log r-2*(r-1)/(r+1)

theorem logGap_derivative {r : ℝ} (hr : 0 < r) :
    HasDerivAt logGap ((r-1)^2/(r*(r+1)^2)) r := by
  have hn : r+1 ≠ 0 := by linarith
  convert (Real.hasDerivAt_log hr.ne').sub
    ((((hasDerivAt_id r).sub_const 1).const_mul 2).div
      ((hasDerivAt_id r).add_const 1) hn) using 1
  simp only [id_eq]
  field_simp; ring

theorem logarithmic_mean_bound {r : ℝ} (hr : 1 ≤ r) :
    2*(r-1)/(r+1) ≤ Real.log r := by
  have hm : MonotoneOn logGap (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      exact (logGap_derivative (by have : 1 ≤ t := ht; linarith)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 1 < t := by simpa only [interior_Ici] using ht
      exact (logGap_derivative (by linarith)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 1 < t := by simpa only [interior_Ici] using ht
      rw [(logGap_derivative (by linarith : 0<t)).deriv]
      positivity
  have h := hm (by simp) hr hr
  norm_num [logGap] at h
  linarith

theorem noise_delay_bound {r : ℝ} (hr : 1 < r) :
    4 ≤ 2*(r+1)/(r-1)*Real.log r := by
  have h := logarithmic_mean_bound hr.le
  have hc : 0 ≤ 2*(r+1)/(r-1) := div_nonneg (by linarith) (by linarith)
  have hh := mul_le_mul_of_nonneg_left h hc
  have hz : 2*(r+1)/(r-1)*(2*(r-1)/(r+1))=4 := by
    have h1 : r-1 ≠ 0 := by linarith
    have h2 : r+1 ≠ 0 := by linarith
    field_simp; ring
  rwa [hz] at hh

theorem receiver_background (C V W : ℝ) :
    (C-W)+(W/2+(V+W/2))=C+V ∧ W/2-(V+W/2)=-V := by constructor <;> ring

theorem receiver_exchange (Cp Vp Wp H C W : ℝ)
    (h : Cp+3*H*C+Vp=0) :
    (Cp-Wp+3*H*(C-W))+(Vp+Wp+3*H*W)=0 := by linear_combination h

theorem receiver_tradeoff (f g Om : ℝ) (hf : f ≠ 0) (ho : Om ≠ 0) :
    f*(2*g^2/(3*f*Om))=2*g^2/(3*Om) := by field_simp; ring

theorem loading_reciprocity (load eps c H : ℝ) (hl : load ≠ 0) (he : eps ≠ 0) :
    (load*eps*c*H)*(1/(load*eps))=c*H := by field_simp; ring

theorem different_loading_changes_acceleration (l1 l2 eps c H : ℝ)
    (hl : l1 ≠ l2) (he : eps ≠ 0) (hc : c ≠ 0) (hH : H ≠ 0) :
    l1*eps*c*H ≠ l2*eps*c*H := by
  intro h
  apply hl
  exact mul_right_cancel₀ he (mul_right_cancel₀ hc (mul_right_cancel₀ hH h))

def tt (p q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![p,q,0; q,-p,0; 0,0,0]

theorem tt_norm (p q : ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, (tt p q i j)^2)=2*(p^2+q^2) := by
  simp [tt, Fin.sum_univ_three]; ring

theorem tt_coordinates (p q p' q' : ℝ) (h : tt p q=tt p' q') : p=p' ∧ q=q' := by
  constructor
  · have := congrFun (congrFun h 0) 0; simpa [tt] using this
  · have := congrFun (congrFun h 0) 1; simpa [tt] using this

theorem tt_spans (a b c d e f : ℝ) (ht : a+d+f=0)
    (hc : c=0) (he : e=0) (hf : f=0) :
    (!![a,b,c; b,d,e; c,e,f] : Matrix (Fin 3) (Fin 3) ℝ)=tt a b := by
  have hd : d = -a := by rw [hf] at ht; linarith
  subst c; subst e; subst f; subst d; rfl

theorem tensor_energy_nonnegative (Z a p q dp dq k : ℝ) (hZ : 0 ≤ Z) (ha : 0 ≤ a) :
    0 ≤ Z*a/4*(dp^2+dq^2+k^2*(p^2+q^2)) := by positivity

theorem tensor_luminal_symbol (w k p : ℝ) (hp : p ≠ 0) (h : (w^2-k^2)*p=0) :
    w^2=k^2 := by
  have hh := (mul_eq_zero.mp h).resolve_right hp
  linarith

/-- A positive shear kinetic correction changes tensor speed while a static
calculation has no time-derivative term. Excluding it is a physical premise. -/
theorem tensor_speed_deformation (M s : ℝ) (hM : 0 < M) (hs : 0 < s) :
    0 < M/(M+s) ∧ M/(M+s) < 1 := by
  have hd : 0 < M+s := by linarith
  exact ⟨div_pos hM hd, (div_lt_one hd).mpr (by linarith)⟩

theorem kinetic_correction_static (s hdot : ℝ) (h : hdot=0) :
    s*hdot^2=0 := by rw [h]; ring

theorem adiabatic_stock_scaling (m r v : ℝ) (hm : m ≠ 0)
    (hr : r=1/m^3) (hv : v=m^2) :
    m*v*r=1 ∧ v^2=m/r ∧ v^4=m^8 := by
  rw [hr, hv]
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · ring

theorem two_pole_tracking (n1 n2 q qd gamma omega K1 K2 : ℝ → ℝ) (t0 : ℝ)
    (h1 : ∀ t, HasDerivAt n1 (gamma t*(q t-n1 t)) t)
    (h2 : ∀ t, HasDerivAt n2 (omega t*(n1 t-n2 t)) t)
    (hq : ∀ t, HasDerivAt q (qd t) t)
    (hK1 : ∀ t, HasDerivAt K1 (gamma t) t)
    (hK2 : ∀ t, HasDerivAt K2 (omega t) t)
    (hw : ∀ t, 0 ≤ omega t)
    (hfall : ∀ t, t0 ≤ t → qd t ≤ 0)
    (ha : q t0 ≤ n1 t0) (hb : q t0 ≤ n2 t0) :
    ∀ t, t0 ≤ t → q t ≤ n2 t := by
  have hn1 := passive_lag_sign n1 q qd gamma K1 t0 h1 hq hK1 hfall ha
  have hn2 := regular_rate_positivity (fun t => n2 t-q t) K2 omega
    (fun t => omega t*(n1 t-q t)-qd t) t0
    (fun t => by convert (h2 t).sub (hq t) using 1 <;> ring) hK2
    (fun t ht => by
      have hnn : 0 ≤ omega t*(n1 t-q t) := mul_nonneg (hw t) (sub_nonneg.mpr (hn1 t ht))
      have hq' := hfall t ht
      change 0 ≤ omega t*(n1 t-q t)-qd t
      linarith)
    (by change 0 ≤ n2 t0-q t0; linarith)
  intro t ht; have h := hn2 t ht; dsimp at h; linarith

theorem relabeling_cancels (u R du dR gamma : ℝ)
    (hu : du = -gamma*u) (hR : dR = gamma*u) : du+dR=0 := by
  rw [hu,hR]; ring

theorem cubic_is_least_degree_C2_join (a b c d : ℝ)
    (h0 : a=0) (h1 : b=0) (h2 : 2*c=0) :
    (fun z : ℝ => a+b*z+c*z^2+d*z^3) = (fun z => d*z^3) := by
  have hc : c=0 := by linarith
  subst a; subst b; subst c; funext z; ring

end ConnectedClosure
