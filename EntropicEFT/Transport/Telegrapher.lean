import EntropicEFT.Transverse.RankOne

/-!
# EntropicEFT.Transport.Telegrapher

LOCAL CONTRACT
* Manuscript: Section 17; Appendix E.1--E.2.
* Closed algebra: causal parameter relation, canonical H0 branch, quadratic-mode roots
  specification, and exact static source ratio A/D = kappa/gamma.
* Does not derive: why this is the unique microscopic time-dependent completion.
-/

namespace EntropicEFT.Transport

structure TelegrapherParams where
  tau0 : ℝ
  D : ℝ
  A : ℝ
  c : ℝ
  tau_pos : 0 < tau0
  D_pos : 0 < D
  c_pos : 0 < c
  causalClosure : D/tau0 = c^2

/-- Characteristic polynomial tau s^2 + s + D k^2. -/
noncomputable def characteristic (p : TelegrapherParams) (k s : ℂ) : ℂ :=
  (p.tau0 : ℂ)*s^2 + s + (p.D : ℂ)*(k^2)

/-- Canonical no-new-IR-scale branch. -/
structure CanonicalHubbleTransport extends TelegrapherParams where
  H0 : ℝ
  H0_pos : 0 < H0
  tauHubble : tau0 = 1/H0

namespace CanonicalHubbleTransport

theorem diffusion_closed (p : CanonicalHubbleTransport) : p.D = p.c^2/p.H0 := by
  have hc := p.causalClosure
  rw [p.tauHubble] at hc
  have hH : p.H0 ≠ 0 := ne_of_gt p.H0_pos
  field_simp [hH] at hc ⊢
  nlinarith

end CanonicalHubbleTransport

/-- Source matching needed to recover the static capacity equation. -/
structure StaticTransportMatch where
  kappaOverGamma : ℝ
  params : TelegrapherParams
  sourceRatio : params.A/params.D = kappaOverGamma

/-- Homogeneous cosmological extension remains an explicitly open completion. -/
structure HomogeneousTransportCosmology where
  traceCoupled : Prop
  radiationSuppressed : Prop
  matterEraActive : Prop
  jointBoltzmannClosure : Prop

end EntropicEFT.Transport
