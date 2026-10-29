import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Contact ledger: the acceptance rule and the work register (Appendix O.3)

Ledger kind A. The stock relaxes by local pair contacts (Appendix O.3, "Reciprocal contact with finite
available work"; the contact runs of the dwarf comparison, `dsph_W.py`). Each proposed contact has a change
`dF` of the orbit-averaged mismatch `F` and a change `dK` of the stock's kinetic energy. The rule accepts it when
it lowers `F` and any kinetic energy it adds is covered by the work register `R`; the register pays for heating
and is refunded by cooling. Supernova credits add to `R`.

This module proves what that bookkeeping implies for any sequence of proposals, whatever the dynamics that
generates them:

* `run_ledger`: `K + R` changes only by the credits;
* `run_register_nonneg`: the register never goes negative;
* `run_heating_bounded`: the stock's kinetic energy can rise by at most the initial register plus the credits;
* `spent_register_no_heating`: once the register and the credits are spent, the stock can never end hotter than
  it is, whatever contacts are proposed (the late-time cooling of the dwarf runs);
* `run_mismatch_antitone`: the mismatch never rises;
* `elastic_kinetic_constant`: if every contact conserves kinetic energy, the kinetic energy never changes;
* `gate_after_end`: with contacts switched off after a time `tEnd` (a gas gate), later proposals change
  neither `F` nor `K`.

The momentum and angular-momentum conservation of the individual pair impulses is in `Entropic.StockSettling`
(central pair contacts) and `Entropic.ContactSelection` (`pair_impulse_conserves_angular_momentum`).
Ported from the held-out-test record of 2026-10-26 (`verification/heldout_bestfit_2026-10-26.md`).
-/

noncomputable section

namespace Entropic.ContactLedger

/-- Stock state: mismatch `F`, kinetic energy `K`, work register `R`. -/
structure St where
  F : ℝ
  K : ℝ
  R : ℝ

/-- A proposed pair contact, or a supernova credit to the register. -/
inductive Event
  | contact (dF dK : ℝ)
  | credit (e : ℝ)

/-- The acceptance rule: the contact lowers `F`, and any heating is covered by the register. -/
def Accepts (s : St) (dF dK : ℝ) : Prop := dF < 0 ∧ (dK ≤ 0 ∨ dK ≤ s.R)

open Classical in
/-- One event. An accepted contact moves `dK` between the stock and the register. -/
def step (s : St) : Event → St
  | .contact dF dK => if Accepts s dF dK then ⟨s.F + dF, s.K + dK, s.R - dK⟩ else s
  | .credit e => ⟨s.F, s.K, s.R + e⟩

open Classical in
theorem step_contact (s : St) (dF dK : ℝ) :
    step s (.contact dF dK) = if Accepts s dF dK then ⟨s.F + dF, s.K + dK, s.R - dK⟩ else s := rfl

theorem step_credit (s : St) (e : ℝ) : step s (.credit e) = ⟨s.F, s.K, s.R + e⟩ := rfl

/-- A sequence of events, applied in order. -/
def run : St → List Event → St
  | s, [] => s
  | s, e :: es => run (step s e) es

/-- Total supernova credit in a sequence. -/
def credits : List Event → ℝ
  | [] => 0
  | .credit e :: es => e + credits es
  | .contact _ _ :: es => credits es

/-- Every credit in the sequence is nonnegative. -/
def CreditsNonneg : List Event → Prop
  | [] => True
  | .credit e :: es => 0 ≤ e ∧ CreditsNonneg es
  | .contact _ _ :: es => CreditsNonneg es

theorem step_ledger (s : St) (ev : Event) :
    (step s ev).K + (step s ev).R = s.K + s.R + credits [ev] := by
  cases ev with
  | contact dF dK =>
    rw [step_contact]
    split_ifs <;> simp [credits]
  | credit e =>
    simp [step, credits]
    ring

/-- `K + R` changes only by the supernova credits. -/
theorem run_ledger (s : St) (es : List Event) :
    (run s es).K + (run s es).R = s.K + s.R + credits es := by
  induction es generalizing s with
  | nil => simp [run, credits]
  | cons ev es ih =>
    rw [run, ih (step s ev), step_ledger]
    cases ev with
    | contact dF dK => simp [credits]
    | credit e => simp [credits]; ring

theorem step_register_nonneg (s : St) (ev : Event) (hR : 0 ≤ s.R)
    (hc : ∀ e, ev = .credit e → 0 ≤ e) : 0 ≤ (step s ev).R := by
  cases ev with
  | contact dF dK =>
    rw [step_contact]
    split_ifs with h
    · rcases h with ⟨_, h | h⟩
      · show 0 ≤ s.R - dK; linarith
      · show 0 ≤ s.R - dK; linarith
    · exact hR
  | credit e =>
    show 0 ≤ s.R + e
    have := hc e rfl
    linarith

/-- The register never goes negative. -/
theorem run_register_nonneg (s : St) (es : List Event) (hR : 0 ≤ s.R) (hc : CreditsNonneg es) :
    0 ≤ (run s es).R := by
  induction es generalizing s with
  | nil => simpa [run] using hR
  | cons ev es ih =>
    rw [run]
    cases ev with
    | contact dF dK =>
      exact ih _ (step_register_nonneg s _ hR (by intro e h; cases h)) hc
    | credit e =>
      exact ih _ (step_register_nonneg s _ hR (by intro e' h; cases h; exact hc.1)) hc.2

/-- The stock's kinetic energy can rise by at most the initial register plus the credits. -/
theorem run_heating_bounded (s : St) (es : List Event) (hR : 0 ≤ s.R) (hc : CreditsNonneg es) :
    (run s es).K ≤ s.K + s.R + credits es := by
  have h1 := run_ledger s es
  have h2 := run_register_nonneg s es hR hc
  linarith

/-- Once the register is empty and no credit arrives, the stock cannot end hotter than it is. -/
theorem spent_register_no_heating (s : St) (es : List Event) (hR : s.R = 0) (hc : CreditsNonneg es)
    (h0 : credits es = 0) : (run s es).K ≤ s.K := by
  have := run_heating_bounded s es (le_of_eq hR.symm) hc
  rw [hR, h0] at this
  linarith

theorem step_mismatch_le (s : St) (ev : Event) : (step s ev).F ≤ s.F := by
  cases ev with
  | contact dF dK =>
    rw [step_contact]
    split_ifs with h
    · show s.F + dF ≤ s.F; linarith [h.1]
    · exact le_rfl
  | credit e => exact le_rfl

/-- The mismatch never rises. -/
theorem run_mismatch_antitone (s : St) (es : List Event) : (run s es).F ≤ s.F := by
  induction es generalizing s with
  | nil => exact le_rfl
  | cons ev es ih =>
    rw [run]
    exact le_trans (ih _) (step_mismatch_le s ev)

/-- Every proposed contact conserves kinetic energy. -/
def Elastic : List Event → Prop
  | [] => True
  | .contact _ dK :: es => dK = 0 ∧ Elastic es
  | .credit _ :: es => Elastic es

/-- Under energy-conserving contacts the stock's kinetic energy never changes. -/
theorem elastic_kinetic_constant (s : St) (es : List Event) (h : Elastic es) :
    (run s es).K = s.K := by
  induction es generalizing s with
  | nil => rfl
  | cons ev es ih =>
    rw [run]
    cases ev with
    | contact dF dK =>
      rw [ih _ h.2, step_contact]
      split_ifs
      · show s.K + dK = s.K; rw [h.1]; ring
      · rfl
    | credit e => rw [ih _ h]; rfl

open Classical in
/-- The gas gate: contacts proposed after the end of star formation `tEnd` are dropped;
credits pass. -/
def gate (tEnd : ℝ) : List (ℝ × Event) → List Event
  | [] => []
  | (t, .contact dF dK) :: es => if t ≤ tEnd then .contact dF dK :: gate tEnd es else gate tEnd es
  | (_, .credit e) :: es => .credit e :: gate tEnd es

/-- The sequence contains no contacts. -/
def OnlyCredits : List Event → Prop
  | [] => True
  | .credit _ :: es => OnlyCredits es
  | .contact _ _ :: _ => False

theorem gate_late_only_credits (tEnd : ℝ) (es : List (ℝ × Event)) (h : ∀ p ∈ es, tEnd < p.1) :
    OnlyCredits (gate tEnd es) := by
  induction es with
  | nil => trivial
  | cons p es ih =>
    obtain ⟨t, ev⟩ := p
    have ht : tEnd < t := h (t, ev) (by simp)
    have hrest : ∀ q ∈ es, tEnd < q.1 := fun q hq => h q (by simp [hq])
    cases ev with
    | contact dF dK =>
      unfold gate
      split_ifs with hle
      · exact absurd hle (by linarith)
      · exact ih hrest
    | credit e =>
      unfold gate
      exact ih hrest

theorem run_only_credits (s : St) (es : List Event) (h : OnlyCredits es) :
    (run s es).F = s.F ∧ (run s es).K = s.K := by
  induction es generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons ev es ih =>
    cases ev with
    | contact dF dK => exact absurd h (by simp [OnlyCredits])
    | credit e =>
      rw [run]
      exact ih _ h

/-- After the end of star formation the gated contacts change neither `F` nor `K`. -/
theorem gate_after_end (s : St) (tEnd : ℝ) (es : List (ℝ × Event)) (h : ∀ p ∈ es, tEnd < p.1) :
    (run s (gate tEnd es)).F = s.F ∧ (run s (gate tEnd es)).K = s.K :=
  run_only_credits s _ (gate_late_only_credits tEnd es h)

end Entropic.ContactLedger

end
