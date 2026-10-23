# Retirement report for the v0.8 Prop-label structures (chunk 14, 2026-10-22)

The v0.8 library, merged into this project as `Entropic.EFT` (114 structures), packages its open inputs as structures whose fields are `Prop` labels or typed certificates. Each structure is classified below. Lean names are relative to the `Entropic` namespace.

## 1. Typed certificates instantiated by proofs

| Structure | File | Instance |
|---|---|---|
| GibbsAnalysis | UV/EtaStar.lean | `AppB.Legacy.gibbsAnalysis` |
| EtaStarSpec | UV/EtaStar.lean | `AppB.Legacy.etaStarSpec` |
| UniqueEtaStarCertificate | UV/EtaUniqueness.lean | `AppB.Legacy.uniqueEtaStar` |
| EtaUniquenessMath | UV/EtaUniqueness.lean | `AppB.Legacy.etaUniquenessMath` |
| NumericalSpineCertificate | Numerics/Spine.lean | `AppB.Legacy.numericalSpine` |
| OrthogonalComplementSplit | Representation/SharpTransfer.lean | `Sweep.Legacy.sharpSplit` (P₃ and P_Q on C¹⁶) |
| OrderedPairCountMath | Scale/Leptons.lean | `Sweep.Legacy.orderedPairs` |

## 2. Mathematical packages whose content is proved in `Entropic`

These structures hold `Prop` labels for ordinary mathematics. Their content is proved by the theorems listed; the labels themselves state nothing and are retired.

| Structure | File | Proved by |
|---|---|---|
| UnimodularMath | Cosmology/FixedMeasureDarkEnergy.lean | trace-free equation, integration constant, vacuum shift, w = −1 algebra: `AppO.unimodular_to_einstein`, `AppO.integration_constant`, `AppO.vacuum_shift`, `AppO.constant_mode` (C13-02 to C13-05); the fixed-measure variation is a premise (C13-02) and the contracted Bianchi identity is not formalized (C11-46) |
| ConstrainedDustMath | Cosmology/SaturatedDust.lean | stress tensor on X = ½: `Main.Galactic.dust_stress` (C02-71); the Euler–Lagrange and a⁻³ scaling fields are covered by the C02-71 algebra and `AppO.conserved_fluid` |
| ProjectiveQutritMath | Gauge/ProjectiveColor.lean | projective channel group: `AppIJ.projective_channel` (C10-34 b); M₃ = ℂI ⊕ sl₃ (1 + 8): `Sweep.Alg.units_span`; Wigner-type reversibility not formalized (C10-34 a) |
| GaussianDeterminantMath | Gaussian/RelativeCovariance.lean | `AppH10.determinant_theorem`, `AppH10.gaussian_integral`, `AppH10.det_whiten`, `AppH10.trace_log_form`, `AppH10.legendre_le`, `AppH10.legendre_attained`, `Main.Cosmo.gaussian_kl_nonneg`, `Main.Cosmo.gaussian_kl_quadratic` (C08-02, C08-03, C08-08, C03 Gaussian KL rows) |
| MultiplicativeLapseMath | Gravity/StrongField.lean | `BlackHole.lapse_is_power`, `BlackHole.lapse_exponent_pos`, `BlackHole.f_one` (C06-02) |
| FiniteEntropyFacts | Information/Renewal.lean | mutual information ≥ 0: `AppFG.Info.subadditive`; chain identity: definitions in AppO.Flow with `AppO.H_le_joint`; zero iff product: `AppH1.fixed_marginal_kl`, `AppH1.gibbs` (C07-13) |
| LocalMoveFractureCertificate | Lattice/FiniteRegulator.lean | `AppCDE.MoveGraph.components`, `AppCDE.MoveGraph.pattern_classes`, `AppCDE.MoveGraph.sector_count` (C03-59, C07-18) |
| GaussianLinearizationMath | Marked/CorrectedH9.lean | `Sweep.Ana.gaussian_representation_3d` (C07-54, C01-56) |
| MarkedFiberMath | Marked/CorrectedH9.lean | irreps 0, 1, 2: `AppQ.W.spin1_pair`; Gram identity: `Sweep.Gauss.hermite_gram`; 16 = 7 + 9: `Sweep.SpinPair.projector_split` |
| ZetaNumericalCertificate | Marked/CorrectedH9.lean | enclosure of ζ_*: `AppCDE.zeta_rat`, `Spine.zeta` brackets (C01-07); an instance needs a `MarkedVertexSpec`, whose fields are physical premises |
| JohnsonEdgeSpectrum | Marked/EdgeGraph.lean | `AppH1.johnson_polynomials`, `AppH1.johnson_multiplicities`, `AppH1.A1_sq`, `AppH1.A0_sq` (C07-60) |
| OperatorDoublingRepresentationMath | Marked/SingleStrandRecord.lean | self-duality: `Sweep.SpinPair.dual_commutator`, `Sweep.Dirac.vector_spin_one`; V₁ ⊗ V₁ = V₀ ⊕ V₁ ⊕ V₂: `AppQ.W.spin1_pair` |
| LightestBranchMath | Microstructure/Architecture.lean | `AppH1.lightest_branch` (C07-05) |
| NoSignalingMath | Quantum/Histories.lean | `AppFG.Histories.no_signaling`, `Main.Cosmo.no_signaling` (C06-46, C03-152) |
| ReplacementChannelMath | Quantum/Replacement.lean | `AppFG.Histories.replacement_dual`, `AppH10.replace_props`, `AppH11.replace_tensor` (C03-16, C08-24, C09-02) |
| RecordOverlapTheorem | Quantum/Replacement.lean | `Main.Core.dilation_coherence`, `AppH11.ptr_record`, `AppFG.Histories.environment_overlap` (C01-34, C03-17) |
| UnitMarkedGram | Representation/SharpTransfer.lean | Gram = I₉: `Sweep.Gauss.hermite_gram` (C07-55) |
| FusionThreeHalvesSpec | Representation/FusionSpec.lean | cardinalities 16 = 7 + 9: `Sweep.SpinPair.projector_split`, `AppP.Spin.multiplicities` |
| PositiveScalarSupportLemma | Gaussian/RelativeCovariance.lean | positive scalar rescaling preserves the support (immediate); no separate theorem |
| OneInvariantHessian | Transverse/RankOne.lean | coefficients only (data holder); rank-one Hessian results in `AppKN` (C11, C12 rows) |

## 3. Mathematical packages proved in part or not formalized

| Structure | File | Status |
|---|---|---|
| DiamondGreenMath | Edge/SourceProjection.lean | not formalized: Brillouin-zone representation and Joyce closed form (C05-20, C05-21, C05-22, C11-12, C11-13); G_tet(0) enters as a stated input |
| StaticPDEMath | Gravity/Static.lean | point source: `AppCDE.point_source` (radial form, C05-48 partial); Poisson uniqueness and harmonic decay (Liouville) not formalized (C11-56, C05-50) |
| ThreeModeGroundStateMath | Marked/SingleStrandRecord.lean | not formalized (oscillator Hamiltonian on L²(ℝ³)) |
| EquivariantComplementMatch | Representation/MarkedComplement.lean | multiplicity one by weight counts `AppQ.W.top_weight`; the equivariant intertwiner (C07-51) is not formalized |
| DiagonalMarkedEdgeKernel | Marked/EdgeGraph.lean | S₇ averaging of the 21 edges: `Sweep.Count.average` (C07-62); the off-diagonal-zero field is a selection premise |

## 4. Physical premises and specifications (retained)

These encode physical identifications, completions or empirical readings. They remain premises; the ledger records the corresponding claims as premise-conditional (C) or interpretive (E). Count: 64.

- Clusters/Projection.lean: `ClusterCompletion`
- Core/PhysicalInterfaces.lean: `FoundationSpec`, `MarkedFusionIncidence`, `SurvivalGapMassBridge`, `SameClosureCouplingMarkedSource`, `CommonGeometryCapacityLimit`, `FixedContinuumEventMeasure`, `VolumeConjugacy`, `CausticReleaseBridge`, `EqualIRConversionNormalization`, `ReleaseTriggerIndependentOfClosure`, `GeometricEmbeddingSpec`, `TransverseInfluenceSpec`, `StrongBoundarySpec`, `ArrowOfTimeSpec`
- Cosmology/FixedMeasureDarkEnergy.lean: `RoutingEnergyBridge`, `FixedMeasureGravity`, `LambdaSourceLaw`, `ReleaseHistory`, `InitialLambdaZeroSpec`
- Cosmology/SaturatedDust.lean: `PinnedCommittedBranch`, `CommittedReleaseSpec`, `CarrierExclusionLedger`
- Edge/Kernel.lean: `MinimalReturnCompletion`, `EuclideanNormalizationSpec`
- Edge/SourceProjection.lean: `ExclusionSufficiency`
- Foundations/Postulates.lean: `ContinuumSymmetryTarget`
- Gauge/FactorSplit.lean: `RelationalCapacityGaugeSplit`
- Gauge/ProjectiveColor.lean: `PersistentOpenRoute`, `MinimalColorKineticCompletion`, `StandardModelCompletion`
- Gauge/VertexRealization.lean: `DecoratedVertexModel`
- Gaussian/RelativeCovariance.lean: `GFTGeometricRelativeInfoBridge`
- Gravity/Static.lean: `EinsteinScalarReduction`, `BaselineNoSlipSpec`
- Gravity/StrongField.lean: `SphericalEinsteinReduction`, `CapacityExhaustionInterpretation`, `HorizonAreaBridge`
- Information/Renewal.lean: `MaximumCaliberSelection`, `LayerEntropyBudget`
- Lattice/FiniteRegulator.lean: `CapacityDecoratedCDTTarget`
- Marked/CorrectedH9.lean: `MarkedVertexSpec`
- Marked/SingleStrandRecord.lean: `SingleResponsePhasePoint`, `SingleStrandEvent`, `TwoDepositEvent`, `SingleStrandCanonicalRealization`, `ChainRecordAlternativeSpec`
- Microstructure/Architecture.lean: `SevenLayerHistoryReading`, `OperatorSeparation`, `NativeRenewalGate`, `DecoratedGeometricAction`
- OpenProblems/Interfaces.lean: `RemainingCompletion`
- Quantum/Histories.lean: `QuantumKinematics`, `DecoherentHistoryFamily`, `GleasonRecordMeasure`, `ManyPastsReading`
- Quantum/Replacement.lean: `NoWhichPathCondition`
- Representation/FusionSpec.lean: `PhysicalFusionRecord`
- Scale/Electron.lean: `ElectronAnchorSpec`
- Scale/Leptons.lean: `ShellSpectrumCollapse`, `ShellMassDressingSpec`
- Transport/Telegrapher.lean: `HomogeneousTransportCosmology`
- Transverse/RankOne.lean: `GalacticCompletion`
- UV/BranchAudit.lean: `BranchSelectionCriterion`

## 5. Data carriers and bookkeeping (no claim content)

- `ClusterDataStatus` (Clusters/Projection.lean), `RatInterval` (Core/Prelude.lean), `Bridge` (Core/Prelude.lean), `ModelPremise` (Core/Prelude.lean), `ClaimRecord` (Core/Status.lean), `ConditionalResult` (Core/Status.lean), `TheoryInputs` (Foundations/Postulates.lean), `OperationalQuantumInputs` (Foundations/Postulates.lean), `CapacityFieldPoint` (Gravity/FieldDefinitions.lean), `BoundedCapacityPoint` (Gravity/FieldDefinitions.lean), `ToyRealization` (Instantiation/ToyCDT.lean), `FiniteLatticeData` (Lattice/FiniteRegulator.lean), `EmpiricalComparisonInputs` (Numerics/Spine.lean), `TelegrapherParams` (Transport/Telegrapher.lean), `CanonicalHubbleTransport` (Transport/Telegrapher.lean), `StaticTransportMatch` (Transport/Telegrapher.lean), `PortAssignment` (UV/Boundary.lean), `BoundaryCode` (UV/Boundary.lean)

Totals: 7 instantiated, 20 proved in content, 5 partial or not formalized, 64 physical premises, 18 data carriers (114 structures).
