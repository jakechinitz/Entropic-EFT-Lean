import EntropicEFT.Marked.CorrectedH9

/-!
# EntropicEFT.Scale.Electron

LOCAL CONTRACT
* Manuscript: Sections 2, 13; Appendices D.4, H.6, H.9.
* Closed algebra: recurrence, survival gap formula, electron-anchored L*, induced G* identity.
* Physical bridge exposed: identifying the lowest positive charged survival gap with the
  electron rest energy and the same spectral tick with causal length.
* Empirical input: electron mass is an anchor, not predicted here.
-/

namespace EntropicEFT.Scale
open EntropicEFT.Marked

/-- Seven-layer state-weighted determinant recurrence. -/
noncomputable def recurrence (g : ℝ) : ℝ := Real.exp (-7*g)

/-- Positive-survival raw dimensionless logarithmic gap. -/
noncomputable def rawLogGap (g : ℝ) : ℝ := -Real.log (1 - recurrence g)

/-- Reduced Compton wavelength. -/
noncomputable def reducedCompton (hbar m c : ℝ) : ℝ := hbar / (m*c)

/-- Baseline unmarked electron scale. -/
noncomputable def L0 (hbar me c g : ℝ) : ℝ :=
  -(3/2 : ℝ) * reducedCompton hbar me c * Real.log (1 - recurrence g)

/-- Marked physical scale. -/
noncomputable def Lstar (hbar me c g ζ : ℝ) : ℝ := Ze ζ * L0 hbar me c g

/-- Induced gravitational normalization. -/
noncomputable def Gstar (hbar me c g ζ : ℝ) : ℝ :=
  inducedG c hbar (Lstar hbar me c g ζ)

/-- Algebraic closed form quoted in the manuscript. -/
theorem Gstar_closed_form {hbar me c g ζ : ℝ}
    (hh : hbar ≠ 0) (hm : me ≠ 0) (hc : c ≠ 0) :
    Gstar hbar me c g ζ =
      (9/4 : ℝ) * (hbar*c/me^2) * (Ze ζ)^2 *
        (Real.log (1 - recurrence g))^2 := by
  simp [Gstar, inducedG, Lstar, L0, reducedCompton]
  field_simp [hh, hm, hc]
  ring

/-- Physical/empirical package needed to interpret the algebra as the substrate length. -/
structure ElectronAnchorSpec where
  c : ℝ
  hbar : ℝ
  me : ℝ
  c_pos : 0 < c
  hbar_pos : 0 < hbar
  me_pos : 0 < me
  survivalGapMass : SurvivalGapMassBridge
  survivalGapMassHolds : survivalGapMass.holds
  sameTickSetsLength : Prop

/-- The baseline 3/2 factor is the reciprocal of the 2/3 transverse export; it is kept
separate from the H.9/O.13 Gaussian 3/2. -/
noncomputable def transverseExportInverse : ℝ := 3/2

end EntropicEFT.Scale
