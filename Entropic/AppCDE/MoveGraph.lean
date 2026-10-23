import Entropic.FiniteModel
import Entropic.AppB.Counts
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! Ordering sectors of the single-label move class (ledger C05-60). A move changes one
slot of an injective labeling by ±1 and must stay injective. Within each orientation copy
the move graph on the 840 states has exactly 24 = 4! connected components, one per
relative order of the four slot values, each with 35 = C(7,4) states. -/

namespace Entropic.AppCDE.MoveGraph
open Entropic.FiniteModel

def moves (s : FaceState) : List FaceState :=
  let (a, b, c, d) := s
  [(a+1, b, c, d), (a-1, b, c, d), (a, b+1, c, d), (a, b-1, c, d),
   (a, b, c+1, d), (a, b, c-1, d), (a, b, c, d+1), (a, b, c, d-1)]

def Adj (s t : FaceState) : Prop := t ∈ moves s ∧ t ∈ states

/-- Relative order of the four slot values. -/
def pattern (s : FaceState) : List Bool :=
  let (a, b, c, d) := s
  [decide (a < b), decide (a < c), decide (a < d), decide (b < c), decide (b < d), decide (c < d)]

def sumv (s : FaceState) : Int := s.1 + s.2.1 + s.2.2.1 + s.2.2.2

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem moves_symm : ∀ s t : FaceState, t ∈ moves s → s ∈ moves t := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [moves, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ <;> simp [moves]

theorem adj_symm {s t : FaceState} (hs : s ∈ states) (h : Adj s t) : Adj t s :=
  ⟨moves_symm s t h.1, hs⟩

def valid (t : FaceState) : Bool :=
  let (a, b, c, d) := t
  decide (-3 ≤ a ∧ a ≤ 3 ∧ -3 ≤ b ∧ b ≤ 3 ∧ -3 ≤ c ∧ c ≤ 3 ∧ -3 ≤ d ∧ d ≤ 3 ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)

theorem mem_labels (x : Int) : x ∈ labels ↔ -3 ≤ x ∧ x ≤ 3 := by
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem mem_states_iff (t : FaceState) : t ∈ states ↔ valid t = true := by
  obtain ⟨a, b, c, d⟩ := t
  rw [Entropic.AppB.mem_states]
  simp only [valid, decide_eq_true_eq, mem_labels]
  tauto

theorem pattern_invariant' : states.all (fun s => (moves s).all (fun t => !valid t || pattern t == pattern s)) = true := by
  decide

/-- Moves preserve the order pattern. -/
theorem pattern_invariant : ∀ s ∈ states, ∀ t ∈ moves s, t ∈ states → pattern t = pattern s := by
  intro s hs t ht hts
  have := List.all_eq_true.mp pattern_invariant' s hs
  have := List.all_eq_true.mp this t ht
  rw [mem_states_iff] at hts
  simpa [hts] using this

/-- 24 patterns, 35 states each. -/
theorem pattern_classes : ((states.map pattern).dedup.length = 24) ∧
    ∀ p ∈ (states.map pattern).dedup, (states.filter fun s => pattern s = p).length = 35 := by
  decide

/-- Descent: every state other than a ground state (labels {−3,−2,−1,0}) has a move that lowers
the label sum. -/
theorem descent' : states.all (fun s => sumv s == -6 || (moves s).any (fun t => valid t && decide (sumv t < sumv s))) = true := by
  decide

theorem descent : ∀ s ∈ states, sumv s = -6 ∨ ∃ t ∈ moves s, t ∈ states ∧ sumv t < sumv s := by
  intro s hs
  have := List.all_eq_true.mp descent' s hs
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h | ⟨t, ht, hv, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, ht, (mem_states_iff t).mpr hv, hlt⟩

/-- Ground states are determined by their pattern. -/
theorem ground_nodup : ((states.filter fun s => sumv s = -6).map pattern).Nodup := by decide

theorem ground_unique : ∀ s ∈ states, ∀ t ∈ states, sumv s = -6 → sumv t = -6 →
    pattern s = pattern t → s = t := by
  intro s hs t ht h1 h2 hp
  exact List.inj_on_of_nodup_map ground_nodup (List.mem_filter.mpr ⟨hs, by simp [h1]⟩)
    (List.mem_filter.mpr ⟨ht, by simp [h2]⟩) hp

theorem sumv_ge : ∀ s ∈ states, -6 ≤ sumv s := by decide

/-- Every state reaches the ground state of its pattern. -/
theorem reach_ground : ∀ n : ℕ, ∀ s ∈ states, (sumv s + 6).toNat = n →
    ∃ g ∈ states, sumv g = -6 ∧ pattern g = pattern s ∧ Relation.ReflTransGen Adj s g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hn
    rcases descent s hs with h0 | ⟨t, htm, hts, hlt⟩
    · exact ⟨s, hs, h0, rfl, Relation.ReflTransGen.refl⟩
    · have hge := sumv_ge t hts
      obtain ⟨g, hg, hg0, hgp, hpath⟩ := ih (sumv t + 6).toNat (by omega) t hts rfl
      exact ⟨g, hg, hg0, hgp.trans (pattern_invariant s hs t htm hts),
        Relation.ReflTransGen.head ⟨htm, hts⟩ hpath⟩

theorem path_symm {s t : FaceState} (hs : s ∈ states) (h : Relation.ReflTransGen Adj s t) :
    Relation.ReflTransGen Adj t s := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hst hab ih =>
    exact Relation.ReflTransGen.head (adj_symm (by
      rcases Relation.ReflTransGen.cases_tail hst with h | ⟨c, _, hc⟩
      · rw [h]; exact hs
      · exact hc.2) hab) ih

/-- Connected components = order patterns: two states are joined by moves iff they have the
same relative order. -/
theorem components (s t : FaceState) (hs : s ∈ states) (ht : t ∈ states) :
    Relation.ReflTransGen Adj s t ↔ pattern s = pattern t := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | @tail b c hst hab ih =>
      have hb : c ∈ states := hab.2
      have ha : b ∈ states := by
        rcases Relation.ReflTransGen.cases_tail hst with h | ⟨e, _, he⟩
        · rw [h]; exact hs
        · exact he.2
      rw [ih ha]
      exact (pattern_invariant _ ha _ hab.1 hb).symm
  · intro hp
    obtain ⟨g, hg, hg0, hgp, h1⟩ := reach_ground _ s hs rfl
    obtain ⟨g', hg', hg0', hgp', h2⟩ := reach_ground _ t ht rfl
    have : g = g' := ground_unique g hg g' hg' hg0 hg0' (by rw [hgp, hgp', hp])
    subst this
    exact h1.trans (path_symm ht h2)

/-- 2 orientations × 24 sectors × 35 states = 1680. -/
theorem sector_count : 2 * 24 * 35 = 1680 ∧ Nat.choose 7 4 = 35 ∧ Nat.factorial 4 = 24 := by decide

end Entropic.AppCDE.MoveGraph
