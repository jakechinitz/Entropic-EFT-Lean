# Manuscript-to-Lean map

The map is intentionally many-to-many. A manuscript section can contain exact algebra, a physical bridge, empirical evidence, and an open task; those belong in different Lean modules.

| Manuscript | Primary Lean module(s) | Formal status |
|---|---|---|
| 1--4 Foundations / definitions / dependency map | `Foundations/Postulates`, `Core/PhysicalInterfaces`, `Gravity/FieldDefinitions`, `Quantum/Histories` | premises + bookkeeping |
| 5 Tetrahedral boundary ensemble | `UV/Boundary`, `Representation/SpinDimensions` | finite exact + UV premise |
| 6 Admissibility closure | `UV/ClosureInvariant`, `UV/Spectrum`, `UV/Admissibility`, `UV/EtaStar`, `UV/EtaUniqueness` | finite exact; real-analysis certificate pending |
| 7--9 edge kernel / loops / stiffness | `Edge/TetrahedralFrame`, `Edge/Kernel`, `Edge/SourceProjection` | exact algebra; return operator conditional |
| 10--14 static Einstein branch / electron / no slip | `Gravity/Static`, `Scale/Electron`, `Marked/CorrectedH9`, `Quantum/Replacement` | exact algebra + external GR math + physical anchor |
| 15--16 galaxy / lensing | `Transverse/RankOne` | rank-one algebra exact; influence/lensing open |
| 17 transport | `Transport/Telegrapher` | branch algebra exact/conditional |
| 18 clusters | `Clusters/Projection` | bookkeeping exact; microscopic/empirical completion open |
| 19 cosmology / Hubble tension | `Transport/Telegrapher` | structured open extension |
| 20 saturated phase / CMB | `Cosmology/SaturatedDust` | exact reciprocal algebra; pinned/recruitment conditional |
| 21 strong field | `Gravity/StrongField` | algebra + external spherical GR; substrate boundary open |
| 22 Many-Pasts | `Quantum/Histories`, `Information/Renewal`, `OpenProblems/Interfaces` | operational QM external math; arrow open |
| 23 microstructure Hamiltonian | `Microstructure/Architecture`, `Marked/CorrectedH9` | finite marked action; geometric completion open |
| 24 lattice tests | `Lattice/FiniteRegulator` | exact regulator identities + empirical certificates |
| 25 equilibrium vacuum / cosmological term | `Lattice/FiniteRegulator`, `Cosmology/FixedMeasureDarkEnergy` | finite centering exact; continuum inference conditional |
| 26 closure-status table | `Audit/ClaimLedger` | metadata |
| 27--30 falsifiers/comparisons/conclusion | `Audit/ClaimLedger`, `OpenProblems/Interfaces` | status/falsifier map, not proofs |
| Appendix A conventions | `Core/Prelude`, `Gravity/FieldDefinitions` | definitions |
| Appendix B UV ensemble | `UV/*`, `Representation/*` | principal finite exact core |
| Appendix C edge/source | `Edge/*` | exact + conditional return operator |
| Appendix D weak field / electron | `Gravity/Static`, `Scale/Electron`, `Information/Renewal` | exact algebra + named bridges |
| Appendix E transport | `Transport/Telegrapher` | branch algebra |
| Appendix F spherical strong field | `Gravity/StrongField` | external GR math + open boundary |
| Appendix G Many-Pasts | `Quantum/Histories`, `Information/Renewal` | operational/external math + open typicality |
| Appendix H microstructure / H.9 / H.10 / H.11 | `Microstructure/Architecture`, `Marked/CorrectedH9`, `Marked/SingleStrandRecord`, `Marked/EdgeGraph`, `Gaussian/RelativeCovariance`, `Quantum/Replacement` | finite marked algebra + conditional one-strand record realization + open embedding |
| Appendix I mass/gauge | `Scale/Leptons`, `Gauge/ProjectiveColor` | finite shell algebra + conditional gauge route |
| Appendix J lattice | `Lattice/FiniteRegulator` | exact regulator + empirical/open |
| Appendix K checks | `Numerics/Spine`, `tools/audit.py` | independent reproducibility layer |
| Appendix L fork accounting | `UV/BranchAudit`, `Audit/ClaimLedger` | finite branch/status audit |
| Appendix M CMB carrier no-go | `Cosmology/SaturatedDust` | exclusion ledger; empirical/math inputs separated |
| Appendix N parent action | `Gravity/Static`, `Gravity/StrongField`, `Transverse/RankOne`, `Gaussian/RelativeCovariance` | exact targets + external math/open transverse |
| Appendix O dark energy | `Cosmology/FixedMeasureDarkEnergy`, `Marked/SingleStrandRecord` | stationary ratio exact inside selected one-strand ledger; physical realization/continuum/release bridges conditional |
| Appendix P reproduction | `tools/audit.py`, `Numerics/Spine` | deterministic reproduction + interval target |
