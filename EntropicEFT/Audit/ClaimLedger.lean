import EntropicEFT.Core.Status

/-!
# EntropicEFT.Audit.ClaimLedger

LOCAL CONTRACT
* Manuscript: Section 26.
* Purpose: machine-readable index of the principal closure-status rows.
* This is metadata.  The theorem/module named by a row remains the authority.
-/

namespace EntropicEFT.Audit
open EntropicEFT

private def claim (id moduleName manuscript conclusion : String)
    (status : ClaimStatus) (assumptions : List String := []) : ClaimRecord where
  id := id
  status := status
  moduleName := moduleName
  manuscript := manuscript
  assumptions := assumptions
  conclusion := conclusion

/-- Compact machine-readable ledger.  Empirical comparisons intentionally do not appear as proofs. -/
def principalClaims : List ClaimRecord := [
  claim "uv.count.1680" "UV.Boundary" "B.1/B.4" "2 P(7,4)=1680" .closed,
  claim "uv.k2.spectrum" "UV.Spectrum" "B.2" "complete eleven-value K^2 spectrum" .closed,
  claim "uv.k2.split" "UV.ClosureInvariant" "B.2/H.9" "K^2=|c|^2+V_q" .closed,
  claim "uv.eta.stationary" "UV.Admissibility" "B.2" "eta <K^2>=3/2 at stationarity" .closed,
  claim "uv.eta.unique" "UV.EtaUniqueness" "B.2" "unique global evidence maximum" .externalMath,
  claim "rep.7plus9" "Representation.FusionSpec" "B.4/H.9" "V_3 plus V_0+V_1+V_2" .externalMath,
  claim "rep.incidence" "Core.PhysicalInterfaces" "B.4/H.9" "marked fiber is nonmaximal fusion record" .conditional,
  claim "info.refresh" "Information.Renewal" "D.4/G/H" "unique input-independent replacement kernel" .closed,
  claim "quantum.renewal" "Quantum.Replacement" "H.8/H.11" "replacement/record-overlap channel theorems" .externalMath,
  claim "marked.vertex" "Marked.CorrectedH9" "H.9" "finite marked routing algebra" .fixed
    ["same closure coupling in minimal marked source"],
  claim "marked.record.finite" "Marked.SingleStrandRecord" "H.9/O.13"
    "one selected strand: 3 pairs, 3/2 ledger; 9 operator labels; two-copy control: 6 pairs, 3" .closed,
  claim "marked.record.realization" "Marked.SingleStrandRecord" "H.9/O.13"
    "HS auxiliary is the one canonical strand and history is its operator-dual record end" .conditional
    ["canonical oscillator realization", "operator doubling", "difference-sign W_*", "fresh strand per vertex"],
  claim "scale.electron" "Scale.Electron" "D.4/H.9" "electron-anchored L* and induced G*" .conditional
    ["survival gap/rest-energy bridge"],
  claim "edge.tree" "Edge.Kernel" "C" "tree edge coupling" .closed,
  claim "edge.loop" "Edge.Kernel" "C" "minimal return completion" .conditional,
  claim "source.map" "Edge.SourceProjection" "C/D" "Green-matched source projection" .closed,
  claim "gravity.static" "Gravity.Static" "D/N" "capacity form of Newton scalar action" .externalMath,
  claim "gravity.matchedG" "Gravity.Static" "C/D" "matched G equals c^3 L*^2/hbar identically" .closed,
  claim "gaussian.relative" "Gaussian.RelativeCovariance" "H.10" "Gaussian determinant/KL functional" .externalMath,
  claim "gft.embedding" "Core.PhysicalInterfaces" "H.10/J/N" "stable covariant geometric embedding" .open,
  claim "galaxy.rankone" "Transverse.RankOne" "15/N" "rank-one one-invariant Hessian" .closed,
  claim "galaxy.rar" "Transverse.RankOne" "15/N" "thermal RAR completion" .conditional,
  claim "transport.telegrapher" "Transport.Telegrapher" "17/E" "D/tau=c^2 branch" .fixed,
  claim "cosmo.dust" "Cosmology.SaturatedDust" "20/M" "pinned committed dust" .conditional,
  claim "cosmo.reciprocity" "Cosmology.SaturatedDust" "20" "a0*(Omega_c/Omega_b)=cH0" .closed,
  claim "dark.fixedmeasure" "Cosmology.FixedMeasureDarkEnergy" "O.1" "unimodular reduction" .conditional,
  claim "dark.lambda0" "Cosmology.FixedMeasureDarkEnergy" "O.5" "initial Lambda zero" .conditional,
  claim "dark.eta" "Cosmology.FixedMeasureDarkEnergy" "O.13" "release routing eta=eta*" .conditional
    ["single-strand canonical realization", "record ledger is physical routed energy",
     "equal IR conversion", "release trigger unbiased in K^2"],
  claim "strong.spherical" "Gravity.StrongField" "F/N" "spherical GR q_geo first integral" .externalMath,
  claim "strong.boundary" "Core.PhysicalInterfaces" "F/N" "physical termination at q=0" .open,
  claim "manypasts.operational" "Quantum.Histories" "G" "Born/no-signaling operational branch" .externalMath,
  claim "manypasts.arrow" "Core.PhysicalInterfaces" "G" "substrate arrow typicality" .open,
  claim "leptons.shells" "Scale.Leptons" "I.1" "finite shell/routing mass algebra" .fixed,
  claim "color.route" "Gauge.ProjectiveColor" "I.2" "projective qutrit color route" .conditional,
  claim "lattice.finite" "Lattice.FiniteRegulator" "J" "finite-regulator simulation results" .empirical,
  claim "lattice.continuum" "Lattice.FiniteRegulator" "J.9" "capacity-decorated CDT continuum limit" .open,
  claim "cluster.maps" "Clusters.Projection" "18" "resolved baryonic-map lensing test" .open
]

end EntropicEFT.Audit
