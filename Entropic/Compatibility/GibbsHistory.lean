import Entropic.ClosureRoot
import Entropic.Compatibility.History

/-! A full-support 1680-state Gibbs law, using the certified spectrum, and
its exactly normalized finite product histories. Unlike the finite shell
cycle, this construction really uses the native nonuniform Gibbs marginal.
States are indexed by energy and degeneracy; no physical geometric network
or infinite-history Hilbert-space completion is inferred from this index.
-/
noncomputable section
open scoped BigOperators
namespace Entropic.Compatibility.GibbsHistory
open Entropic.ClosureRoot

def multiplicity : Fin 11 → ℕ := ![96,96,96,288,192,144,384,192,48,96,48]
def level : Fin 11 → ℝ := ![122/3,134/3,142/3,146/3,152/3,154/3,158/3,162/3,164/3,166/3,170/3]
abbrev Microstate := (i : Fin 11) × Fin (multiplicity i)

theorem state_count : Fintype.card Microstate=1680 := by
  simp only [Microstate, Fintype.card_sigma, Fintype.card_fin]
  simp [multiplicity, Fin.sum_univ_succ]

def weight (eta : ℝ) (s : Microstate) := Real.exp (-eta*level s.1)
def probability (eta : ℝ) (s : Microstate) := weight eta s/Z eta

theorem weight_sum (eta : ℝ) : (∑ s : Microstate, weight eta s)=Z eta := by
  rw [Fintype.sum_sigma]
  simp only [weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [Z, specR, level, multiplicity, Fin.sum_univ_succ]
  <;> ring

theorem probability_positive (eta : ℝ) (s : Microstate) : 0 < probability eta s :=
  div_pos (Real.exp_pos _) (Z_pos eta)

theorem probability_normalized (eta : ℝ) : (∑ s, probability eta s)=1 := by
  unfold probability
  rw [← Finset.sum_div, weight_sum, div_self (Z_pos eta).ne']

theorem native_history_normalized (eta : ℝ) (n : ℕ) :
    (∑ h : Fin n → Microstate, History.historyWeight (probability eta) n h)=1 :=
  History.history_normalized _ (probability_normalized eta) n

theorem native_history_full_support (eta : ℝ) (n : ℕ) (h : Fin n → Microstate) :
    0 < History.historyWeight (probability eta) n h :=
  History.history_positive _ (probability_positive eta) n h

theorem native_history_consistent (eta : ℝ) (h : Fin n → Microstate) :
    (∑ s, History.historyWeight (probability eta) (n+1) (History.extend h s))=
      History.historyWeight (probability eta) n h :=
  History.consistent_prefix _ (probability_normalized eta) h

theorem native_archive_size (n : ℕ) : Fintype.card (Fin n → Microstate)=1680^n := by
  rw [History.archive_size, state_count]

end Entropic.Compatibility.GibbsHistory
