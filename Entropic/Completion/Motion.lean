import Entropic.StockSettling

/-! Contacts with positions allowed to evolve. This closes the finite schedule
composition gap in StockSettling. It is a mechanical integrator identity, not
a convergence theorem for Einstein/Vlasov or proof that a galaxy target is selected. -/
noncomputable section
open Finset Matrix
namespace Entropic.Completion.Motion
open Entropic.StockSettling

structure State (N : ℕ) where
  x : Fin N → Fin 3 → ℝ
  p : Fin N → Fin 3 → ℝ

def drift {N : ℕ} (m : Fin N → ℝ) (dt : ℝ) (s : State N) : State N :=
  ⟨fun i => s.x i+(dt/m i) • s.p i,s.p⟩
def kick {N : ℕ} (c : Contact N) (s : State N) : State N :=
  ⟨s.x,applyContact s.x c s.p⟩
def advance {N : ℕ} (m : Fin N → ℝ) (dt : ℝ) (c : Contact N) (s : State N) :=
  drift m dt (kick c s)

theorem drift_conserves {N : ℕ} (m : Fin N → ℝ) (dt : ℝ) (s : State N) :
    totalMomentum (drift m dt s).p=totalMomentum s.p ∧
    angularMomentum (drift m dt s).x (drift m dt s).p=angularMomentum s.x s.p := by
  constructor
  · rfl
  · simp [drift,angularMomentum,map_add,LinearMap.add_apply,cross_self]

theorem advance_conserves {N : ℕ} (m : Fin N → ℝ) (dt : ℝ) (c : Contact N) (s : State N) :
    totalMomentum (advance m dt c s).p=totalMomentum s.p ∧
    angularMomentum (advance m dt c s).x (advance m dt c s).p=angularMomentum s.x s.p := by
  obtain ⟨h1,h2⟩ := drift_conserves m dt (kick c s)
  exact ⟨h1.trans (contact_momentum s.x c s.p),h2.trans (contact_angular s.x c s.p)⟩

def evolve {N : ℕ} (m : Fin N → ℝ) : List (ℝ × Contact N) → State N → State N
  | [],s => s
  | (dt,c)::rest,s => evolve m rest (advance m dt c s)

theorem evolution_conserves {N : ℕ} (m : Fin N → ℝ) (events : List (ℝ × Contact N)) (s : State N) :
    totalMomentum (evolve m events s).p=totalMomentum s.p ∧
    angularMomentum (evolve m events s).x (evolve m events s).p=angularMomentum s.x s.p := by
  induction events generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons e rest ih =>
    obtain ⟨h1,h2⟩ := ih (advance m e.1 e.2 s)
    obtain ⟨g1,g2⟩ := advance_conserves m e.1 e.2 s
    exact ⟨h1.trans g1,h2.trans g2⟩

theorem drift_reversible {N : ℕ} (m : Fin N → ℝ) (dt : ℝ) (s : State N) :
    drift m (-dt) (drift m dt s)=s := by
  cases s
  simp [drift,neg_div,neg_smul]

end Entropic.Completion.Motion
