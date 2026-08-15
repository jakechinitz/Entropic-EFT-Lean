import EntropicEFT.Gaussian.RelativeCovariance

/-!
# EntropicEFT.Transverse.RankOne

LOCAL CONTRACT
* Manuscript: Section 15; Appendix N.8.
* Closed algebra: one-invariant leading potential has a rank-one 2x2 Hessian,
  `C_cross^2 = A_L A_T`, and the clamped static response ratio.
* Physical/open: loading one sharing entropy into the action cell, horizon coupling,
  retarded influence functional, and transverse metric/lensing kernel.
-/

namespace EntropicEFT.Transverse

/-- Hessian coefficients from V = F(DeltaC) at DeltaC=0. -/
structure OneInvariantHessian where
  fpp : ℝ
  dL : ℝ
  dT : ℝ

namespace OneInvariantHessian

noncomputable def AL (h : OneInvariantHessian) : ℝ := h.fpp*h.dL^2
noncomputable def AT (h : OneInvariantHessian) : ℝ := h.fpp*h.dT^2
noncomputable def Ccross (h : OneInvariantHessian) : ℝ := h.fpp*h.dL*h.dT

theorem rank_one_identity (h : OneInvariantHessian) :
    h.Ccross^2 = h.AL*h.AT := by
  simp [Ccross, AL, AT]
  ring

/-- Static minimization of the transverse coordinate at fixed longitudinal source. -/
noncomputable def clampedSlope (h : OneInvariantHessian) : ℝ := -h.Ccross/h.AT

end OneInvariantHessian

/-- Two action-angle pairs have angular Haar volume (2pi)^2. -/
noncomputable def twoAngleVolume : ℝ := (2*Real.pi)^2

/-- Conditional compact two-phase acceleration scale. -/
noncomputable def a0 (gShare c H0 : ℝ) : ℝ := gShare / twoAngleVolume * c*H0

theorem a0_closed (gShare c H0 : ℝ) :
    a0 gShare c H0 = gShare/(4*Real.pi^2)*c*H0 := by
  unfold a0 twoAngleVolume
  ring

/-- Bose occupation used by the selected clamped thermal reading. -/
noncomputable def boseOccupation (x : ℝ) : ℝ := 1/(Real.exp x - 1)

/-- Conditional RAR response. -/
noncomputable def rarAcceleration (gbar a0val : ℝ) : ℝ :=
  gbar * (1 + boseOccupation (Real.sqrt (gbar/a0val)))

/-- All non-algebraic physical content of the galactic completion is explicit here. -/
structure GalacticCompletion where
  influence : TransverseInfluenceSpec
  oneSharingEntropyLoaded : Prop
  reversibleHorizonCoupling : Prop
  clampedOscillatorReading : Prop
  hbarOmegaEqualsHorizonTemperature : Prop
  environmentIndependentAT : Prop

end EntropicEFT.Transverse
