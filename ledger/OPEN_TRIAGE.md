# Triage of the 196 open claims (2026-10-22)

Each open claim is assigned to a group by the mathematics it needs. Importance says how much of the paper rests on the group. Tractability: T1 decidable or elementary, T2 needs one reusable development, T3 substantial development, T4 outside Mathlib today (kept as cited results). Chunk is the work chunk in PLAN.md.

## Major holes

1. Newton limit and Phi = Psi (G3, G4): field equations of the reduced action, conformally flat curvature, harmonic decay. Plan: first-variation theorem, coordinate curvature, maximum principle.
2. Spherical reduction and the Schwarzschild sector (G4): warped-product curvature, reduced action, vacuum field equations. Plan: coordinate computation for the static diagonal metric first.
3. Field equations of the galactic actions (G3): carrier, QUMOND-type and director Euler-Lagrange equations, momentum balance.
4. Equivariant uniqueness (G1): frame lock up to phase, block phases on Q, commutant of the marked fiber. Plan: Schur lemma for ladder matrices of every spin.
5. Lie closure of the retained sector (G7): so(9), su(9), su(81). Plan: abstract generation lemma, certified ranks where the kernel can carry them.
6. The value G_tet(0) = 0.44822 (G9, G10): enters the Newton constant. The Joyce evaluation is out of reach; a certified Gamma(1/3) enclosure is attempted.
7. Graviton TT sector and rigging maps (G10): unbounded-operator analysis; kept as cited standard results.

## Highest leverage

- Schur lemma for ladder irreps (G1): about 12 claims.
- First-variation theorem with compact support (G3): about 15 claims.
- Coordinate curvature and maximum principle (G4): about 15 claims.
- Reclassification of simulation and data rows (G12): 19 rows that are not theorems.

## Groups

### G1. Schur lemma, commutants, equivariant uniqueness (16 claims)
- Importance: core (marked vertex, frame lock, gauge construction)
- Tractability: T2: one ladder-matrix Schur lemma for every spin unlocks the group
- Chunk: 15

  - C03-24 Frame lock unique up to phase (Schur)
  - C15-10 Schur form of the one-cell lock
  - C15-11 Blockwise uniqueness of locks on Q_cap
  - C04-72 Block-phase freedom of equivariant complement isometries
  - C07-51 Unique isometric intertwiner Q → H_mark
  - C07-126 Commutant of the marked fiber
  - C04-37 Schur block decomposition of covariant Hessian
  - C10-38 Uniqueness of the frame-invariant quadratic form on the adjoint
  - C14-73 Spin-3/2 pair channel: commutant dimensions and gap
  - C14-80 Face-pair and two-pair commutants; irreducibility on networks
  - C09-09 Real form of the complement Q
  - C15-04 Matching transfer and its limit
  - C14-75 Intertwiner space dimension and vanishing transported bilinears
  - C04-51 Equivariant lock propagates under maximal blocking
  - C15-13 Equivariant lock under maximal blocking (Lemma)
  - C09-31 Tensor-product factorization from commuting full matrix algebras

### G2. Top multiplet, coherent states, Heisenberg kernels (8 claims)
- Importance: core (maximal fusion and blocking)
- Tractability: T3: needs tensor-power group actions; concrete N = 2 cases first
- Chunk: 19

  - C03-26 Maximal fusion map on coherent states
  - C04-50 Coherent states under F_N
  - C07-81 Coherent-state fusion identities
  - C08-31 Coherent maximal-fusion kinematics
  - C15-14 Coherent-state blocking
  - C04-58 Kernel of bond sum on connected graph
  - C08-39 Kernel of nearest-neighbour alignment Hamiltonian
  - C08-40 One-magnon reduction and vanishing gap

### G3. First variation and integration by parts on R^n (20 claims)
- Importance: core (field equations of the carrier, QUMOND and director actions; Newton limit)
- Tractability: T2: one first-variation theorem for compactly supported variations unlocks most of the group
- Chunk: 16

  - C01-45 Field equations of the reduced action and Phi = Psi
  - C01-47 Covariant reduced-functional field equation
  - C02-11 Euler-Lagrange equations of the QUMOND-type action
  - C02-12 Excess (transverse) Poisson equation
  - C11-55 Constraint equations
  - C11-57 Newton action from substitution
  - C11-58 Pre-variation identification loses a constraint
  - C12-02 Euler-Lagrange equations of the carrier action
  - C12-07 Director Euler-Lagrange equation
  - C02-21 Variable-stiffness κ term reduces to a connection cross term
  - C11-52 Integrated-by-parts quadratic form
  - C12-13 Stock variation of the stiffness energy
  - C02-24 Momentum balance of joint-source excess forces
  - C12-15 Force from stationary directors and momentum balance
  - C02-22 Tilt expansion and coherence length
  - C02-23 Midplane excess of the near-radial director
  - C11-98 Varying-frame kinetic expansion
  - C12-10 Axisymmetric director energy density
  - C03-76 Newtonian potential solution and point-source profile
  - C12-53 Hermiticity of the static Dirac Hamiltonian

### G4. Coordinate GR: weak field, spherical reduction, maximum principle (27 claims)
- Importance: core (Newton limit, Phi = Psi, Schwarzschild sector)
- Tractability: T2 to T3: curvature formulas proved in coordinates; Liouville via the maximum principle
- Chunk: 17

  - C11-50 Scalar curvature of a conformally flat 3-metric
  - C11-51 Second-order expansion of N sqrt(h) ^(3)R
  - C01-44 Static ADM reduction of Einstein-Hilbert to quadratic order
  - C03-133 No slip from scalar constraint
  - C11-56 Harmonic difference vanishes for isolated sources
  - C06-05 Warped-product scalar curvature decomposition
  - C11-66 Warped-product curvature identity
  - C11-67 Angular reduction of the Einstein-Hilbert action
  - C11-68 Reduced spherical action after integration by parts
  - C06-08 Reduced vacuum field equations
  - C11-71 Vacuum Euler-Lagrange equations
  - C06-07 Boundary extrinsic curvature split and reduced GHY term
  - C11-69 Extrinsic curvature of a product boundary
  - C11-70 Reduced GHY coefficient
  - C12-81 Conformal-factor form of the Euclidean action
  - C12-62 Integrated scalar curvature in the sector
  - C11-46 Matter conservation from the Bianchi identity
  - C07-118 Point-particle stress tensor
  - C07-119 Einstein equations from ordinary action
  - C07-122 Geodesic equation from worldline action
  - C12-30 Linear Ward identity from Bianchi; covariance of carrier maps
  - C09-63 Lorentzian kernel counting
  - C13-46 Linearized capacity perturbation equations
  - C13-47 Synchronous-gauge reduction
  - C09-59 Schläfli Hessian at a flat simplex
  - C09-60 Bloch-assembled Hessian annihilates gauge modes
  - C03-100 Regge four-volumes of (4,1) and (3,2) simplices

### G5. Matrix calculus, ODE, Haar moments and quantum-information inequalities (27 claims)
- Importance: supporting (clock, Weyl ordering, DeWitt measure)
- Tractability: T2 to T4
- Chunk: 18

  - C03-49 Mass derivative of Omega(m)
  - C12-46 Memory (variation-of-constants) formula
  - C12-48 Differential of g(C)
  - C09-84 Integrated clock response (Duhamel)
  - C12-84 Integrated proper clock (Duhamel) and cocycle
  - C09-79 Mass-conjugate clock monotonicity and bounds
  - C09-90 Exact marked rest gap with polar-normalized transport
  - C12-49 DeWitt kinetic matrix: determinant and signature
  - C12-54 Configuration-space determinants
  - C12-57 Weyl scalar coefficients
  - C12-72 DeWitt line element in volume-shape variables
  - C12-73 Homogeneous Weyl constraint in volume-shape variables
  - C12-74 Flat-density congruence
  - C12-78 Conformal/shape split of the kinetic matrix
  - C12-56 Weyl symbol of a quadratic kinetic term
  - C12-58 Weyl vs Laplace-Beltrami ordering
  - C12-59 Weyl-ordered constraint commutators
  - C12-63 Constraint algebra in the sector
  - C12-66 Continuous-configuration current
  - C12-82 Gaussian integration of the conformal mode
  - C15-30 Exact orthogonal kinetic decomposition
  - C14-70 Microcanonical form and entropy increase
  - C14-68 Relative-entropy contraction under a channel with fixed point
  - C14-71 Primitivity implies geometric convergence
  - C07-36 Quadratic fluctuation spectrum
  - C10-39 Haar second moment for a qutrit
  - C10-44 Haar projector moment identities

### G6. Finite combinatorics and explicit linear algebra (18 claims)
- Importance: supporting
- Tractability: T1 to T3: decidable once the objects are defined
- Chunk: 18

  - C01-59 Routing-block state count
  - C14-89 Label-ledger enumeration (O.15)
  - C10-83 Timelike-triangle counting identity
  - C07-106 Dirac–Kähler zero modes and Betti numbers
  - C10-49 Per-site oriented area tensors on D_diamond x Z
  - C10-32 Primitive recoupling overlaps equal -1/20
  - C09-53 Connected-pair kernel parametrization and determinant
  - C09-54 Kernel dimension of the all-edge parent on a connected graph
  - C09-49 Fusion map and polar normalization
  - C15-43 S_4 character identity and equivariant encoding
  - C15-58 Symmetric count states and collective raising operator
  - C15-72 Connected-interface ranks
  - C15-60 First count gap values
  - C07-113 Hinge amplitude from Cauchy equations
  - C07-111 Equal face areas imply disphenoid
  - C10-101 Lipschitz lower bound on distance
  - C10-72 Gaussian field integration and spanning-tree entropy
  - C03-56 Spanning-tree entropy from Gaussian integration

### G7. Lie-algebra closure (11 claims)
- Importance: core (su(9), su(81) kinematics of the retained sector)
- Tractability: T3: abstract generation lemma plus certified ranks; large ranks may exceed the kernel
- Chunk: 19

  - C03-19 Two-mark bridge generates su(81)
  - C09-34 Two-mark Lie closure su(81)
  - C14-34 Pair-generator Lie closure is sl(16) / su(16)
  - C14-36 Matching operator spans all nine bilinears
  - C14-39 Compressed rotations close to so(9)
  - C14-41 so(9) plus one traceless symmetric generator gives su(9)
  - C14-43 Tensor-product Lie generation lemma
  - C14-44 Three-slot algebra sl(64)
  - C14-45 Network controllability by spanning-tree induction
  - C14-50 Two retained marks: su(81)
  - C15-31 Lie closure gives su(9)

### G8. Ensemble numerics at eta_* (9 claims)
- Importance: supporting (channel costs, defect response)
- Tractability: T2: certified finite sums with the existing exp bounds
- Chunk: 19

  - C14-08 Numerical range of the seven channel costs
  - C14-11 Jensen excess and marginal anisotropy (numerical)
  - C14-19 Perimeter record from joint face admissibility (numerical)
  - C14-21 Face entropies and mutual information of the square-root vacuum
  - C14-22 Defect-response table (numerical)
  - C14-23 Comparative inequalities drawn from the table
  - C04-86 Prior-tilt sensitivities of g and G_*
  - C04-87 Prior-tilt sensitivity of muon ratio
  - C03-55 Closure-sector vacuum admissibility 0.536

### G9. Special functions and stated-input arithmetic (11 claims)
- Importance: core for G_tet(0) via Gamma(1/3); peripheral otherwise
- Tractability: T2 to T4
- Chunk: 18

  - C05-22 Numerical value of G_tet(0)
  - C11-12 Numerical value of the Joyce closed form
  - C09-70 F(1) as a Beta value and limiting interval gap
  - C13-27 s -> infinity limiting minimum
  - C02-47 Wide-binary Jacobi radius and tidal corrections
  - C02-65 Bullet projection numbers
  - C03-163 RAR boost at z = 0 and z = 2.3
  - C03-165 MUSE redshift projection
  - C13-37 Cumulative release vs vacuum fractions by z=2
  - C02-43 Galactic tide magnitude vs Cassini
  - C02-46 Minimum smoothing lengths from Cassini 2σ

### G10. Unbounded operators, distributions, lattice Green functions (25 claims)
- Importance: core (graviton sector, rigging, G_tet(0) integral) but outside Mathlib
- Tractability: T4: kept as cited standard results
- Chunk: none (cited results)

  - C08-33 Form compression of the master constraint
  - C08-61 Strong-resolvent convergence to Z_G(-Delta)P_TT
  - C08-62 Strong-resolvent convergence of the Hamiltonians
  - C08-63 Massless TT spectrum
  - C08-70 Convergence of Gaussian characteristic functionals
  - C08-85 Capacity-decorated rigging lift
  - C08-87 Finite-regulator group averaging
  - C08-88 Clock-test-space formula
  - C08-90 Strong-resolvent convergence implies rigging-form convergence
  - C08-91 Positivity and constraint annihilation of the limiting form
  - C08-92 Regularity of smeared spectral density
  - C08-93 Feynman boundary value and Plemelj
  - C15-21 Rigging-map lift and physical-space isomorphism
  - C03-75 Mosco convergence implies Green-function convergence
  - C09-37 Infinite-volume quasi-local dynamics and GNS
  - C03-70 Green function of conserved transport ~ 1/(4 pi D r)
  - C03-73 Lattice Green function with O(a^2/r^3) correction
  - C05-11 Point-source response Q(0) = s G_tet(0)/J
  - C05-20 Diamond on-site Green function as Brillouin-zone integral
  - C05-21 Joyce closed form for G_tet(0)
  - C11-13 Diamond-lattice Green function equals Joyce value
  - C07-14 Entropy-rate ceiling and i.i.d. equality case (H.4 form)
  - C13-77 Closed-cohort mutual-information dissipation
  - C07-84 Overcomplete coherent family resolves the ray
  - C08-30 Support of the 3N-restricted delta

### G11. Convex geometry and topology (5 claims)
- Importance: peripheral
- Tractability: T4: kept as cited results
- Chunk: none (cited results)

  - C06-19 Cauchy surface-area formula: mean projected area = A/4
  - C07-78 Minkowski reconstruction of a tetrahedron
  - C07-96 Weyl node charges sum to zero
  - C09-24 One-mark state space is CP^8
  - C14-79 Density of gluing products in SO(3)

### G12. Simulation outputs, data fits, unstated inputs (19 claims)
- Importance: not theorems
- Tractability: reclassify as numerical or data records
- Chunk: 20

  - C01-41 Shell-target crossing
  - C02-25 Milky Way-LMC Plummer force numbers
  - C03-74 128^3 periodic Laplacian fit
  - C03-82 Screening-length bound xi > 4.6
  - C03-84 Effective Green dimension
  - C04-33 Induced-fraction benchmarks
  - C05-41 Pair-volume spectrum
  - C05-43 Minimum RMS face-cosine deviation at j=3
  - C13-30 Plummer projection check
  - C13-33 NFW stock vs RAR response agreement
  - C13-42 Nonlinear spherical exhaustion check
  - C13-43 Linear-depletion vs positive allocation at fixed history
  - C13-54 Numerical stock-evolution witnesses
  - C13-75 Poisson coverage estimate
  - C13-86 Reference-split invariance numerics
  - C13-96 Pair abundance and annihilation rate at k_B T = m_e c^2
  - C14-56 PPF benchmark calibration values
  - C14-93 Miscellaneous reproduced numbers in the register
  - C15-61 TT count-oscillator gap ratios
