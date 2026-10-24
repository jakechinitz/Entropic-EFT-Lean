import Mathlib

/-! Algebraic electromagnetic extension. The operator relations are explicit
hypotheses; no assertion identifies them with native Astra gluing. The rotor
identity is pointwise on sequences, not a self-adjointness or evolution theorem.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.Electromagnetism

def comm {A : Type*} [Ring A] (a b : A) : A := a*b-b*a

theorem comm_product {A : Type*} [Ring A] (g a b : A) :
    comm g (a*b) = comm g a*b+a*comm g b := by
  simp only [comm]
  noncomm_ring

theorem comm_sum {A : Type*} [Ring A] (g a b : A) :
    comm g (a+b) = comm g a+comm g b := by
  simp only [comm]
  noncomm_ring

theorem independent_gauge_invariant_coefficient {A : Type*} [Ring A] [Algebra ℂ A]
    (g h : A) (beta : ℂ) (hh : comm g h=0) : comm g (beta • h)=0 := by
  simp only [comm, mul_smul_comm, smul_mul_assoc, ← smul_sub]
  change beta • comm g h=0
  rw [hh, smul_zero]

theorem weighted_product {A : Type*} [Ring A] [Algebra ℂ A]
    (g a b : A) (r s : ℂ)
    (ha : comm g a = r • a) (hb : comm g b = s • b) :
    comm g (a*b) = (r+s) • (a*b) := by
  rw [comm_product, ha, hb, smul_mul_assoc, mul_smul_comm, add_smul]

theorem charged_hop_commutes {A : Type*} [Ring A] [Algebra ℂ A]
    (g creation link annihilation : A) (dx dy : ℂ)
    (hc : comm g creation = (-dx) • creation)
    (hu : comm g link = (dx-dy) • link)
    (ha : comm g annihilation = dy • annihilation) :
    comm g (creation*link*annihilation) = 0 := by
  rw [weighted_product g (creation*link) annihilation _ dy
    (weighted_product g creation link (-dx) (dx-dy) hc hu) ha]
  convert zero_smul ℂ (creation*link*annihilation) using 1
  congr 1
  ring

theorem number_preserves_bilinear {A : Type*} [Ring A] [Algebra ℂ A]
    (n creation annihilation : A)
    (hc : comm n creation = creation) (ha : comm n annihilation = -annihilation) :
    comm n (creation*annihilation) = 0 := by
  have h := weighted_product n creation annihilation (1:ℂ) (-1)
    (by simpa using hc) (by simpa using ha)
  simpa using h

theorem weighted_list_product {A : Type*} [Ring A] [Algebra ℂ A]
    (g : A) (ops : List (A × ℂ))
    (hh : ∀ p ∈ ops, comm g p.1=p.2 • p.1) :
    comm g (ops.map Prod.fst).prod = (ops.map Prod.snd).sum • (ops.map Prod.fst).prod := by
  induction ops with
  | nil => simp [comm]
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact weighted_product g p.1 (ps.map Prod.fst).prod p.2 (ps.map Prod.snd).sum
      (hh p (by simp)) (ih (fun q hq => hh q (by simp [hq])))

theorem closed_loop_commutes {A : Type*} [Ring A] [Algebra ℂ A]
    (g : A) (ops : List (A × ℂ))
    (hh : ∀ p ∈ ops, comm g p.1=p.2 • p.1)
    (closed : (ops.map Prod.snd).sum=0) : comm g (ops.map Prod.fst).prod=0 := by
  rw [weighted_list_product g ops hh, closed, zero_smul]

theorem loop_four_commutes {A : Type*} [Ring A] [Algebra ℂ A]
    (g a b c d : A) (r s t u : ℂ)
    (ha : comm g a = r • a) (hb : comm g b = s • b)
    (hc : comm g c = t • c) (hd : comm g d = u • d)
    (closed : r+s+t+u=0) : comm g (a*b*c*d)=0 := by
  rw [weighted_product g (a*b*c) d _ u
    (weighted_product g (a*b) c _ t
      (weighted_product g a b r s ha hb) hc) hd, closed, zero_smul]

theorem finite_sum_commutes {A I : Type*} [Ring A] [Fintype I]
    (g : A) (h : I → A) (hh : ∀ i, comm g (h i)=0) :
    comm g (∑ i, h i)=0 := by
  simp only [comm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_eq_zero (fun i _ => hh i)

theorem kernel_preserved {V : Type*} [AddCommGroup V] [Module ℂ V]
    (g h : Module.End ℂ V) (hc : g*h=h*g) (v : V) (hv : g v=0) :
    g (h v)=0 := by
  have hh := congrArg (fun f : Module.End ℂ V => f v) hc
  simpa [Module.End.mul_apply, hv] using hh

def gaugeLink {V : Type*} (g : V → ℂˣ) (u : ℂˣ) (x y : V) : ℂˣ :=
  g x*u*(g y)⁻¹

theorem closed_four_link_gauge {V : Type*} (g : V → ℂˣ)
    (u v w z : ℂˣ) (a b c d : V) :
    gaugeLink g u a b*gaugeLink g v b c*gaugeLink g w c d*gaugeLink g z d a =
      u*v*w*z := by
  simp only [gaugeLink]
  group
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem hopping_phase_invariant (gx gy px py u : ℂ)
    (hx : star gx*gx=1) (hy : star gy*gy=1) :
    star (gx*px)*(gx*u*star gy)*(gy*py)=star px*u*py := by
  rw [star_mul]
  calc
    _ = (star gx*gx)*(star gy*gy)*(star px*u*py) := by ring
    _ = _ := by rw [hx,hy]; ring

def flux (f : ℤ → ℂ) (n : ℤ) : ℂ := (n:ℂ)*f n
def raiseFlux (f : ℤ → ℂ) (n : ℤ) : ℂ := f (n-1)
def lowerFlux (f : ℤ → ℂ) (n : ℤ) : ℂ := f (n+1)

theorem rotor_commutator (f : ℤ → ℂ) :
    flux (raiseFlux f)-raiseFlux (flux f)=raiseFlux f := by
  funext n
  simp only [Pi.sub_apply, flux, raiseFlux, Int.cast_sub, Int.cast_one]
  ring

theorem rotor_shift_inverse (f : ℤ → ℂ) : lowerFlux (raiseFlux f)=f := by
  funext n
  simp [lowerFlux, raiseFlux]

theorem closed_graph_total_gauss {V L : Type*} [Fintype V] [Fintype L]
    (inc : V → L → ℝ) (e : L → ℝ) (q : V → ℝ)
    (closed : ∀ l, ∑ x, inc x l=0) :
    (∑ x, ((∑ l, inc x l*e l)-q x)) = -∑ x, q x := by
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, closed, zero_mul]
  simp

theorem physical_closed_graph_neutral {V L : Type*} [Fintype V] [Fintype L]
    (inc : V → L → ℝ) (e : L → ℝ) (q : V → ℝ)
    (closed : ∀ l, ∑ x, inc x l=0)
    (gauss : ∀ x, (∑ l, inc x l*e l)-q x=0) : ∑ x, q x=0 := by
  have h := closed_graph_total_gauss inc e q closed
  simp_rw [gauss] at h
  simpa using h.symm

end Entropic.Electromagnetism
