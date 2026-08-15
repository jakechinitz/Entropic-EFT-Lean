# Section-by-section review notes and cross-connections

This file records what emerged when each formalization cluster was reviewed against downstream modules. These are **audit notes**, not additions to the theory's physical premises.

## 1. Foundations and status ledger

**Review:** The three postulates, finite-capacity premise, tetrahedral architecture, faithful-resolution rule, imported operational quantum kinematics, and continuum symmetry target must remain distinct objects.

**Connection:** Many-Pasts is not needed to prove the Shannon identity selecting an input-independent refresh. It supplies the proposed history ontology in which that refresh is interpreted. The code therefore separates `Information.Renewal` from `Quantum.Histories`.

## 2. UV boundary count

**Review:** The exact state space is four distinguishable ports, seven labels, injectivity from the single-copy channel premise, and two orientations. The closed count is `840*2=1680`.

**Connection:** Injectivity is not generic Pauli antisymmetry. It is specifically the one-copy channel ontology. This premise is therefore visible at the boundary-state definition rather than attributed to SU(2).

## 3. Closure invariant

**Review:** The key exact identity is

```text
K^2 = |c|^2 + V_q,
V_q = 48 - Sigma^2.
```

On the actual injective ensemble:

```text
20/3 <= |c|^2 <= 104/3,
22 <= V_q <= 42.
```

Hence `K^2` and classical closure are nowhere equal.

**Connection to H.9:** This is the formal reason H.9 must Gaussian-linearize only the vector term while retaining the scalar quantum variance in the native amplitude.

**New diagnostic:** At eta* the weighted means are approximately

```text
<|c|^2> = 17.9413036378
<V_q>   = 32.2816117876
<K^2>   = 50.2229154254.
```

Thus the stationary product `eta*<K^2>=3/2` splits numerically into `0.535850... + 0.964150...`. This is a mathematical decomposition only; it is not automatically an energy-routing fraction.

The two components are strongly anticorrelated at eta* (`corr ~ -0.889`), explaining why `Var(K^2)=15.689` is much smaller than either component variance would suggest independently. This may be a useful structural diagnostic of the admissibility ensemble.

## 4. Eta-star and sharing entropy

**Review:** The exact spectrum is sufficient to make eta selection an ordinary finite-Gibbs real-analysis theorem. The repository isolates the remaining calculus/root-isolation work in `UV.EtaUniqueness` rather than treating the decimal root as a primitive.

**Connection:** `eta*<K^2>=3/2` is definitionally downstream of stationarity. It should never be counted again as independent numerical evidence.

## 5. Representation layer and 7+9

**Review:** Dimension arithmetic and actual SU(2) representation content are separate. `16=7+9` and `j=s+1/2` endpoint arithmetic are internal; the Clebsch--Gordan projectors/intertwiner are an ordinary-mathematics certificate until explicitly built.

**Connection:** The physical inference `s=1 -> j0=3/2` still requires the incidence claim that the marked present/history fiber is the complete nonmaximal primitive-fusion record.

## 6. Renewal and quantum coherence

**Review:** The unique input-independent classical refresh can be formalized independently of its physical selection rule. The quantum replacement channel and complementary-record overlap are a second layer.

**Connection:** Position and marked internal fiber must remain in the retained system. A cell-addressed discarded record would multiply a spatial off-diagonal by a nontrivial overlap and decohere motion.

## 7. Corrected H.9 marked vertex

**Review:** The corrected exact factorization is

```text
exp(-eta K^2/2)
= exp(-eta V_q/2) * exp(-eta |c|^2/2).
```

The three-vector Gaussian fixes the normalized response incidence `sqrt eta`. The equality `B_e=sqrt(eta) R_e` then belongs to the selected minimal marked action: it reuses the same coupling and introduces no second coefficient.

**Connection:** This repair preserves all downstream arithmetic `u=8 eta/49`, 21 pair records, zeta*, routing factors, L*, G*, and lepton factors, while making the action's logical premise visible.

**Connection to O.13:** The new `Marked/SingleStrandRecord` audit distinguishes three layers. (i) The repaired HS formula contains one three-coordinate auxiliary. (ii) Under the selected canonical one-strand realization, that auxiliary is completed to exactly three coordinate/momentum pairs, whose unit-frequency vacuum ledger is exactly `3/2`; the nine `V1 x V1*` labels are operator/matrix-unit labels with identity Gram and a difference-sign Liouvillian, not a second oscillator sector. (iii) Interpreting that one-sided stationary ledger as physically released IR energy remains a separate bridge. The HS integral alone does not logically supply conjugate momenta, so layer (ii) is an explicit realization rather than a theorem of Gaussian integration.

**Two-deposit control:** A literal independent-present/independent-history model is a different type with six canonical pairs and vacuum energy `3`. This makes the disputed doubling a model change rather than an ambiguous factor of two.

**Chain control:** An amortized chain model can still carry `3/2` per created strand, but it has an adjacent-record correlation obligation. The selected `SingleStrandCanonicalRealization` instead includes fresh-strand-per-vertex preparation; the repository does not pretend that the bare HS identity alone excludes the chain alternative.

**No missing +1:** The nine record basis elements label first-excitation transition operators. Their difference-sign Liouvillian eigenvalue is zero on the degenerate triplet; they are not occupied one-particle states added to the stationary energy ledger.

## 8. Electron scale and weak-field normalization

**Review:** The algebra from recurrence and marked routing to L* and `G*=c^3 L*^2/hbar` is exact once the survival-gap/rest-energy bridge and electron anchor are adopted.

**New dependency result:** Substituting the Green-matched source map, one-bit mass normalization, and cell-normalized S_infinity into the static Newton coefficient causes the lattice Green constant, `ln 2`, and the stiffness normalization to cancel identically:

```text
G_matched = c^3 L*^2 / hbar.
```

Therefore the matched weak-field G route and electron-induced G* are one normalization chain, not independent evidence.

## 9. Transverse galaxy branch and saturated abundance

**Review:** Rank-one Hessian algebra is exact inside a one-invariant leading EFT; the horizon loading/influence kernel remains physical/open.

**New cross-sector identity:** If both branches use the same epsilon,

```text
a0 = epsilon c H0,
Omega_c/Omega_b = 1/epsilon
```

implies exactly

```text
a0 * (Omega_c/Omega_b) = c H0.
```

The numerical cell value cancels. The identity tests the shared normalization architecture, while each antecedent retains its own physical assumptions.

## 10. Gaussian relative-covariance bridge

**Review:** The determinant ratio, trace-log, convex conjugate, and KL mismatch are pure finite-dimensional mathematics. The identification of a particular decorated GFT Hessian with the geometric operator remains open.

**Connection:** A strictly positive scalar marked factor cannot create/delete a bosonic support direction; this helps reduce the embedding audit but cannot prove common support for the full dressed/equilibrium Hessians.

## 11. Strong field

**Review:** Geometric `q_geo=0` and physical substrate termination are separate. The spherical GR first integral may be formal mathematics while the bounded-domain interpretation remains an open boundary theory.

**Connection:** The `1/4` horizon coefficient is a normalization identity. Turning it into an actual channel-to-area microstate count still needs a physical area operator/counting bridge.

## 12. Fixed measure and dark energy

**Review:** A common factor on fixed-N histories cancels exactly. Fixed event count implying a nondynamical continuum volume form is nevertheless a physical continuum premise. Unimodular tensor identities are ordinary differential geometry downstream of that premise.

**O.13:** Algebraically,

```text
(3/2)/<K^2> = eta*
```

is simply the stationarity relation. The physical statement that this equals a late-time release fraction additionally needs:

1. the proposed record generator to be actual routed IR energy;
2. equal conversion normalization;
3. a release trigger unbiased with respect to internal K².

The corrected H.9 plus `SingleStrandRecord` makes this separation sharper. The mathematical ratio now imports an exact `3/2` from the selected finite one-strand ledger instead of accepting `recordGeneratorExpectation = 3/2` as a free structure field. What remains conditional is the canonical realization itself and its physical release-energy interpretation.

## 13. Gauge-route algebra

**Review:** The projective-qutrit physical reading is conditional, but the route polynomials are exact finite functions of the same tetrahedral labels.

**New connection:** Their sum is an affine complement of the closure invariant:

```text
2(routeA+routeB+routeC) = 144 - 3 K^2.
```

Thus the primitive route sector and UV closure sector share one quadratic tetrahedral data structure; they are not statistically independent finite constructions.

## 14. Lattice, clusters, and empirical sectors

**Review:** Exact centering/energy-origin identities and finite graph arithmetic are appropriate Lean targets. Monte Carlo measurements, observational tables, and likelihoods remain data/certificates. A finite-regulator simulation result must not be promoted to a continuum theorem.

**Connection:** The centered capacity factor and fixed-event dark-energy argument both exploit invariance under an additive extensive energy origin, but they operate at different logical levels: finite-regulator normalization versus continuum volume conjugacy.

## 15. Open completion inventory

The remaining high-value mathematical-physics work is concentrated rather than diffuse:

- explicit SU(2) Clebsch--Gordan/projector construction;
- fully internal eta uniqueness/root certificate;
- finite-loop microscopic return operator;
- EH+GHY reduced-action derivation;
- positive GFT/CDT condensate/support/spectrum calculation;
- covariant Ward/normalization assembly;
- reflection-positive transfer and Lorentzian continuation;
- transverse CTP influence/lensing kernel;
- source-register coherence/release dynamics;
- strong-field capacity boundary action;
- Many-Pasts typicality/arrow theorem;
- physical QCD matter completion.
