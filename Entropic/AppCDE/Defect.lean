import Entropic.AppCDE.GibbsNumerics
import Entropic.AppCDE.Information

/-! Per-type exclusion costs at η* (ledger C05-16 numerics). The 840 unoriented injective
states (orientation doubling cancels from every ratio) are regrouped by K² level; the
per-(face, label) level counts are kernel-checked. -/

noncomputable section
namespace Entropic.AppCDE.Defect
open Entropic.FiniteModel Entropic.ClosureRoot

/-- Regroup a list sum by the values of g (all lying in a duplicate-free list). -/
theorem list_regroup {β : Type*} (L : List β) (g : β → ℤ) (lv : List ℤ) (hlv : lv.Nodup)
    (hall : ∀ s ∈ L, g s ∈ lv) (φ : ℤ → ℝ) :
    (L.map fun s => φ (g s)).sum =
      (lv.map fun k => ((L.filter fun s => g s = k).length : ℝ) * φ k).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : g a ∈ lv := hall a (by simp)
    have ih' := ih (fun s hs => hall s (by simp [hs]))
    have hind : (lv.map fun k => if g a = k then φ k else 0).sum = φ (g a) := by
      rw [← List.sum_toFinset _ hlv, Finset.sum_ite_eq, if_pos (List.mem_toFinset.mpr ha)]
    have hsplit : (lv.map fun k => (((a :: L).filter fun s => g s = k).length : ℝ) * φ k) =
        lv.map (fun k => (if g a = k then φ k else 0) +
          ((L.filter fun s => g s = k).length : ℝ) * φ k) := by
      refine List.map_congr_left (fun k _ => ?_)
      rw [List.filter_cons]
      by_cases h : g a = k <;> simp [h] <;> ring
    rw [List.map_cons, List.sum_cons, ih', hsplit, List.sum_map_add, hind]

def lvls : List ℤ := [122, 134, 142, 146, 152, 154, 158, 162, 164, 166, 170]

set_option maxRecDepth 100000 in
theorem lvls_nodup : lvls.Nodup := by decide

set_option maxRecDepth 100000 in
theorem states_in_lvls : ∀ s ∈ states, threeK2 s ∈ lvls := by decide

def face (i : Fin 4) (s : FaceState) : ℤ :=
  match i with
  | 0 => s.1 | 1 => s.2.1 | 2 => s.2.2.1 | 3 => s.2.2.2

def cnt (L : List FaceState) (k : ℤ) : ℕ := (L.filter fun s => threeK2 s = k).length

def cls : ℤ → List ℕ
  | 3 => [6, 6, 6, 12, 6, 6, 30, 24, 6, 12, 6]
  | 2 => [6, 6, 6, 18, 24, 12, 30, 6, 0, 6, 6]
  | 1 => [6, 12, 6, 30, 6, 12, 30, 6, 6, 6, 0]
  | _ => [12, 0, 12, 24, 24, 12, 12, 24, 0, 0, 0]

set_option maxRecDepth 100000 in
/-- Kernel-checked level counts for every face and every label: they depend only on |m|. -/
theorem table : ∀ i : Fin 4, ∀ l ∈ labels,
    lvls.map (cnt (states.filter fun s => face i s = l)) = cls |l| := by decide

set_option maxRecDepth 100000 in
theorem total_table : lvls.map (cnt states) = [48, 48, 48, 144, 96, 72, 192, 96, 24, 48, 24] := by
  decide

def w (η : ℝ) (k : ℤ) : ℝ := Real.exp (-η * ((k : ℝ) / 3))

theorem regroup_counts (L : List FaceState) (hL : ∀ s ∈ L, threeK2 s ∈ lvls) (η : ℝ) :
    (L.map fun s => w η (threeK2 s)).sum =
      (List.zipWith (fun (c : ℕ) k => (c : ℝ) * w η k) (lvls.map (cnt L)) lvls).sum := by
  rw [list_regroup L threeK2 lvls lvls_nodup hL (w η), List.zipWith_map_left, List.zipWith_self]
  rfl

/-- q-polynomial with the eleven level exponents 0,6,10,12,15,16,18,20,21,22,24. -/
def poly (c : List ℕ) (q : ℝ) : ℝ :=
  (List.zipWith (fun (n : ℕ) (j : ℕ) => (n : ℝ) * q ^ j) c [0, 6, 10, 12, 15, 16, 18, 20, 21, 22, 24]).sum

theorem expand (c : List ℕ) (hc : c.length = 11) (η : ℝ) :
    (List.zipWith (fun (n : ℕ) k => (n : ℝ) * w η k) c lvls).sum =
      Real.exp (-η * (122/3)) * poly c (Real.exp (-η * (2/3))) := by
  match c, hc with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10], _ =>
    simp only [poly, lvls, w, List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons,
      List.sum_nil]
    push_cast
    rw [exp_split η 0 (122/3) (by norm_num), exp_split η 6 (134/3) (by norm_num),
      exp_split η 10 (142/3) (by norm_num), exp_split η 12 (146/3) (by norm_num),
      exp_split η 15 (152/3) (by norm_num), exp_split η 16 (154/3) (by norm_num),
      exp_split η 18 (158/3) (by norm_num), exp_split η 20 (162/3) (by norm_num),
      exp_split η 21 (164/3) (by norm_num), exp_split η 22 (166/3) (by norm_num),
      exp_split η 24 (170/3) (by norm_num)]
    ring

/-- Probability that face i carries label l under p_η (over the 840 unoriented states). -/
def Pfl (i : Fin 4) (l : ℤ) (η : ℝ) : ℝ :=
  ((states.filter fun s => face i s = l).map fun s => w η (threeK2 s)).sum /
    (states.map fun s => w η (threeK2 s)).sum

def Nall : List ℕ := [48, 48, 48, 144, 96, 72, 192, 96, 24, 48, 24]

theorem Pfl_eq (i : Fin 4) (l : ℤ) (hl : l ∈ labels) (η : ℝ) :
    Pfl i l η = poly (cls |l|) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3))) := by
  unfold Pfl
  rw [regroup_counts _ (fun s hs => states_in_lvls s (List.mem_of_mem_filter hs)),
    regroup_counts _ states_in_lvls, table i l hl, total_table]
  have hc : (cls |l|).length = 11 := by
    have : |l| = 3 ∨ |l| = 2 ∨ |l| = 1 ∨ |l| = 0 := by
      simp [labels] at hl; rcases hl with h | h | h | h | h | h | h <;> subst h <;> simp
    rcases this with h | h | h | h <;> rw [h] <;> rfl
  rw [expand _ hc, expand _ rfl, mul_div_mul_left _ _ (Real.exp_pos _).ne']
  rfl

/-- Complement counts N − n per class. -/
def Dcls : ℤ → List ℕ
  | 3 => [42, 42, 42, 132, 90, 66, 162, 72, 18, 36, 18]
  | 2 => [42, 42, 42, 126, 72, 60, 162, 90, 24, 42, 18]
  | 1 => [42, 36, 42, 114, 90, 60, 162, 90, 18, 42, 24]
  | _ => [36, 48, 36, 120, 72, 60, 180, 72, 24, 48, 24]

theorem poly_sub (m : ℤ) (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) (q : ℝ) :
    poly Nall q - poly (cls m) q = poly (Dcls m) q := by
  rcases hm with h | h | h | h <;> subst h <;>
    simp [poly, Nall, cls, Dcls, List.zipWith_cons_cons, List.sum_cons] <;> ring

theorem poly_mono (c : List ℕ) {q b : ℝ} (h0 : 0 ≤ q) (h : q ≤ b) : poly c q ≤ poly c b := by
  unfold poly
  generalize ([0, 6, 10, 12, 15, 16, 18, 20, 21, 22, 24] : List ℕ) = js
  induction c generalizing js with
  | nil => simp
  | cons n c ih =>
    cases js with
    | nil => simp
    | cons j js =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      have : (n:ℝ) * q ^ j ≤ n * b ^ j :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h j) (Nat.cast_nonneg n)
      linarith [ih js]

theorem poly_pos_Nall {q : ℝ} (h0 : 0 ≤ q) : 0 < poly Nall q := by
  simp [poly, Nall, List.zipWith_cons_cons, List.sum_cons]; positivity

/-- The cost c = −ln(1 − P) for class m, as ln of a ratio of positive polynomials. -/
theorem cost_eq (i : Fin 4) (l : ℤ) (hl : l ∈ labels) (η : ℝ) :
    -Real.log (1 - Pfl i l η) =
      -Real.log (poly (Dcls |l|) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) := by
  rw [Pfl_eq i l hl]
  have hN := poly_pos_Nall (Real.exp_pos (-η * (2/3))).le
  have hm : |l| = 0 ∨ |l| = 1 ∨ |l| = 2 ∨ |l| = 3 := by
    simp [labels] at hl; rcases hl with h | h | h | h | h | h | h <;> subst h <;> simp
  rw [← poly_sub _ hm, sub_div, div_self hN.ne']

/-- Certified enclosure of −ln(D(q)/N(q)) from the q-bracket and a Taylor bound. -/
theorem cost_bracket (D : List ℕ) {η a b : ℝ} (h : ClosureStationary η) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hlo : poly D qU / poly Nall qL ≤
      (∑ m ∈ Finset.range 10, (-a) ^ m / m.factorial) - a ^ 10 * (Nat.succ 10 / (Nat.factorial 10 * 10)))
    (hhi : (∑ m ∈ Finset.range 10, (-b) ^ m / m.factorial) + b ^ 10 * (Nat.succ 10 / (Nat.factorial 10 * 10))
      ≤ poly D qL / poly Nall qU)
    (hD : 0 < poly D qL) :
    a ≤ -Real.log (poly D (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ∧
      -Real.log (poly D (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ≤ b := by
  obtain ⟨b1, b2⟩ := stationary_bracket h
  obtain ⟨hL, hU⟩ := Entropic.AppB.q_bracket b1 b2
  set q := Real.exp (-η * (2/3))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hqL0 : (0:ℝ) ≤ qL := by norm_num [qL]
  have hNq := poly_pos_Nall hq0
  have hNL := poly_pos_Nall hqL0
  have hDq : 0 < poly D q := lt_of_lt_of_le hD (poly_mono D hqL0 hL)
  have hx : 0 < poly D q / poly Nall q := div_pos hDq hNq
  have xU : poly D q / poly Nall q ≤ poly D qU / poly Nall qL :=
    div_le_div₀ (le_trans hDq.le (poly_mono D hq0 hU)) (poly_mono D hq0 hU) hNL (poly_mono Nall hqL0 hL)
  have xL : poly D qL / poly Nall qU ≤ poly D q / poly Nall q :=
    div_le_div₀ hDq.le (poly_mono D hqL0 hL) hNq (poly_mono Nall hq0 hU)
  have ea := (Entropic.Spine.exp_neg_encl 10 (by norm_num) ha0 ha1).1
  have eb := (Entropic.Spine.exp_neg_encl 10 (by norm_num) hb0 hb1).2
  constructor
  · have : poly D q / poly Nall q ≤ Real.exp (-a) := le_trans xU (le_trans hlo ea)
    have := Real.log_le_log hx this; rw [Real.log_exp] at this; linarith
  · have : Real.exp (-b) ≤ poly D q / poly Nall q := le_trans eb (le_trans hhi xL)
    have := Real.log_le_log (Real.exp_pos _) this; rw [Real.log_exp] at this; linarith

theorem c3 {η : ℝ} (h : ClosureStationary η) :
    0.14932760369 ≤ -Real.log (poly (Dcls 3) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ∧
      -Real.log (poly (Dcls 3) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ≤ 0.14932760374 :=
  cost_bracket _ h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, qL])

theorem c2 {η : ℝ} (h : ClosureStationary η) :
    0.15402548397 ≤ -Real.log (poly (Dcls 2) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ∧
      -Real.log (poly (Dcls 2) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ≤ 0.15402548403 :=
  cost_bracket _ h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, qL])

theorem c1 {η : ℝ} (h : ClosureStationary η) :
    0.15709998649 ≤ -Real.log (poly (Dcls 1) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ∧
      -Real.log (poly (Dcls 1) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ≤ 0.15709998654 :=
  cost_bracket _ h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, qL])

theorem c0 {η : ℝ} (h : ClosureStationary η) :
    0.15818875742 ≤ -Real.log (poly (Dcls 0) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ∧
      -Real.log (poly (Dcls 0) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3)))) ≤ 0.15818875747 :=
  cost_bracket _ h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, Nall, qL, qU, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [poly, Dcls, qL])

/-- ln(7/6) ∈ (0.1541506798, 0.1541506799). -/
theorem log_seven_sixths : 0.1541506798 < Real.log (7/6) ∧ Real.log (7/6) < 0.1541506799 := by
  have e1 := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.1541506798) (by norm_num) (by norm_num)).1
  have e2 := (Entropic.Spine.exp_neg_encl 10 (by norm_num) (a := 0.1541506799) (by norm_num) (by norm_num)).2
  rw [show Real.log (7/6) = -Real.log (6/7) by rw [← Real.log_inv]; norm_num]
  constructor
  · have : (6/7 : ℝ) < Real.exp (-0.1541506798) := lt_of_lt_of_le (by
      norm_num [Finset.sum_range_succ, Nat.factorial]) e1
    have := Real.log_lt_log (by norm_num) this; rw [Real.log_exp] at this; linarith
  · have : Real.exp (-0.1541506799) < 6/7 := lt_of_le_of_lt e2 (by
      norm_num [Finset.sum_range_succ, Nat.factorial])
    have := Real.log_lt_log (Real.exp_pos _) this; rw [Real.log_exp] at this; linarith

/-- C05-16: over all 28 (label, face) pairs the per-type costs −ln P(A_lf) range over
[0.1493276, 0.1581888] (paper: [0.14933, 0.15819]); their mean lies in
(0.1541564151, 0.1541564152) (paper: 0.15415642) and exceeds ln(7/6) by 5.735·10⁻⁶. -/
theorem defect_costs {η : ℝ} (h : ClosureStationary η) :
    (∀ i : Fin 4, ∀ l ∈ labels,
      0.14932760369 ≤ -Real.log (1 - Pfl i l η) ∧ -Real.log (1 - Pfl i l η) ≤ 0.15818875747) ∧
    (let mean := (1/28) * ∑ i : Fin 4, (labels.map fun l => -Real.log (1 - Pfl i l η)).sum
     0.1541564151 < mean ∧ mean < 0.1541564152 ∧
       5.7352e-6 < mean - Real.log (7/6) ∧ mean - Real.log (7/6) < 5.7355e-6) := by
  obtain ⟨a3, b3⟩ := c3 h; obtain ⟨a2, b2⟩ := c2 h
  obtain ⟨a1, b1⟩ := c1 h; obtain ⟨a0, b0⟩ := c0 h
  have each : ∀ i : Fin 4, (labels.map fun l => -Real.log (1 - Pfl i l η)).sum =
      2 * (-Real.log (poly (Dcls 3) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3))))) +
      2 * (-Real.log (poly (Dcls 2) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3))))) +
      2 * (-Real.log (poly (Dcls 1) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3))))) +
      (-Real.log (poly (Dcls 0) (Real.exp (-η * (2/3))) / poly Nall (Real.exp (-η * (2/3))))) := by
    intro i
    simp only [labels, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [cost_eq i (-3) (by decide), cost_eq i (-2) (by decide), cost_eq i (-1) (by decide),
      cost_eq i 0 (by decide), cost_eq i 1 (by decide), cost_eq i 2 (by decide),
      cost_eq i 3 (by decide)]
    norm_num; ring
  refine ⟨fun i l hl => ?_, ?_⟩
  · rw [cost_eq i l hl]
    have hm : |l| = 0 ∨ |l| = 1 ∨ |l| = 2 ∨ |l| = 3 := by
      simp [labels] at hl; rcases hl with h | h | h | h | h | h | h <;> subst h <;> simp
    rcases hm with hm | hm | hm | hm <;> rw [hm] <;> constructor <;> linarith
  · simp only [Fin.sum_univ_four, each]
    obtain ⟨l1, l2⟩ := log_seven_sixths
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Entropic.AppCDE.Defect
