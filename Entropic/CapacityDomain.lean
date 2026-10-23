import Entropic.BlackHole
import Mathlib.Tactic

/-! Domain of the capacity variable (Sec. 21, App. F.4).

* In flat FRW the spherical invariant about a chosen centre is q_geo = 1 − (H R/c)²
  (`frw_qgeo`). At a fixed event its value depends on the chosen centre
  (`frw_qgeo_center_dependent`), so q_geo is a function of the centre as well as the event.
  It defines a local capacity only where the centre is fixed by the source.
* In the static exterior the source fixes the centre, and q_geo equals the normalized
  Killing norm N² (`static_identification`), positive exactly where static observers
  exist, r > r_s.
* At the horizon the local geometry is regular: the radial tidal acceleration across a
  length ℓ is ℓc⁶/(4(GM)²), decreasing in M (`horizon_tidal_decreasing`), and the
  Kretschmann scalar there is the finite 3c⁸/(4(GM)⁴) (`horizon_kretschmann`).
  Excising the interior is a separate postulate of the capacity identification. -/

noncomputable section
namespace Entropic.CapacityDomain
open Entropic.BlackHole

/-- Flat FRW: Misner–Sharp mass (4/3)πρR³ with Friedmann H² = (8/3)πGρ gives
q_geo = 1 − (HR/c)². -/
theorem frw_qgeo (G c R H ρ : ℝ) (hc : c ≠ 0) (hF : H ^ 2 = 8 / 3 * Real.pi * G * ρ) :
    1 - 2 * G * (4 / 3 * Real.pi * ρ * R ^ 3) / (c ^ 2 * R) = 1 - (H * R / c) ^ 2 := by
  rcases eq_or_ne R 0 with hR | hR
  · subst hR; simp
  · rw [div_pow, mul_pow, hF]; field_simp <;> ring

/-- q_geo of the event at comoving position y, computed about centre z, scale factor a. -/
def qAbout (H a c y z : ℝ) : ℝ := 1 - (H * (a * |y - z|) / c) ^ 2

/-- The same event gets different q_geo about different centres whenever H a ≠ 0. -/
theorem frw_qgeo_center_dependent {H a c y : ℝ} (hH : H ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0) :
    qAbout H a c y y ≠ qAbout H a c y (y + 1) := by
  unfold qAbout
  simp only [sub_self, abs_zero, mul_zero, zero_div, ne_eq]
  rw [show y - (y + 1) = -1 by ring, abs_neg, abs_one, mul_one]
  intro h
  have : (H * a / c) ^ 2 = 0 := by nlinarith
  have : H * a / c = 0 := pow_eq_zero_iff (by norm_num) |>.mp this
  rcases div_eq_zero_iff.mp this with h1 | h1
  · exact (mul_ne_zero hH ha) h1
  · exact hc h1

/-- Hence no function of the event alone reproduces q_geo for every choice of centre. -/
theorem frw_qgeo_not_scalar {H a c : ℝ} (hH : H ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0) :
    ¬ ∃ f : ℝ → ℝ, ∀ y z, qAbout H a c y z = f y := by
  rintro ⟨f, hf⟩
  exact frw_qgeo_center_dependent hH ha hc ((hf 0 0).trans (hf 0 (0 + 1)).symm)

/-- Static exterior: the lapse² of the Killing time equals q_geo, and both are
positive exactly outside r_s (where static observers exist). -/
theorem static_identification {rs r : ℝ} (hrs : 0 < rs) (hr : 0 < r) :
    (0 < qS rs r ↔ rs < r) ∧ (rs < r → Real.sqrt (qS rs r) ^ 2 = qS rs r) :=
  ⟨(qS_sign hrs hr).1, fun h => lapse_sq_eq_qgeo hrs.le h⟩

/-- Radial tidal acceleration across ℓ at r_s = 2GM/c². -/
def horizonTidal (GM c ℓ : ℝ) : ℝ := 2 * GM * ℓ / (2 * GM / c ^ 2) ^ 3

theorem horizon_tidal_eq {GM c ℓ : ℝ} (hGM : GM ≠ 0) (hc : c ≠ 0) :
    horizonTidal GM c ℓ = ℓ * c ^ 6 / (4 * GM ^ 2) := by
  unfold horizonTidal; field_simp <;> ring

/-- It decreases with mass, so the tidal field at a large horizon is weak. -/
theorem horizon_tidal_decreasing {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) :
    StrictAntiOn (fun GM => horizonTidal GM c ℓ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0:ℝ) < x := hx; have hy' : (0:ℝ) < y := hy
  simp only
  rw [horizon_tidal_eq hx'.ne' hc.ne', horizon_tidal_eq hy'.ne' hc.ne']
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  nlinarith

/-- M87* (6.5·10⁹ M_⊙): across 2 m the tidal stretch is below 5·10⁻¹⁰ m s⁻². -/
theorem m87_tidal : horizonTidal (6.5e9 * 1.32712440018e20) 299792458 2 < 5e-10 := by
  rw [horizon_tidal_eq (by norm_num) (by norm_num)]; norm_num

/-- Kretschmann scalar 48(GM)²/(c⁴r⁶) is finite at r_s: 3c⁸/(4(GM)⁴). -/
theorem horizon_kretschmann {GM c : ℝ} (hGM : GM ≠ 0) (hc : c ≠ 0) :
    48 * GM ^ 2 / (c ^ 4 * (2 * GM / c ^ 2) ^ 6) = 3 * c ^ 8 / (4 * GM ^ 4) := by
  field_simp <;> ring

end Entropic.CapacityDomain
