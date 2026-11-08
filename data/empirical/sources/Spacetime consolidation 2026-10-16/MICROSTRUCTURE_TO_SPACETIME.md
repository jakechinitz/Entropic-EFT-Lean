# From microscopic capacity to spacetime

## Consolidated derivations and reasoning

Research checkpoint, 16 October 2026, evening revision. Prepared for Jake. The original source snapshot was completed at 19:09 UTC, about 3:09 pm Eastern. This edition adds the subsequent connected CDT, native clock, and joint orbital constructions. The afternoon explanation is preserved under `editions/2026-10-16-afternoon`. The manuscript, research originals, frozen source copies, original ZIP, and running experiments are unchanged by this explanatory update.

The work now includes an explicit finite model in which geometry changes while retained matter moves and accumulates proper-clock response. Its empty-particle sector reproduces an enumerated CDT transfer, its selected geometry transport preserves the native rest-energy gap exactly, and an explicit microscopic cochain metric preserves the combined operator. The earlier capacity construction, bare curvature normalization, and Einstein saddle remain part of the derivation. The interacting long-distance gravitational response has not yet been established.

The connected argument has four layers. The finite capacity ensemble supplies the local state and charged rest gap. Coherent binary bonds, the selected angular rule, and paired-cell volume calibration supply a bare curvature coefficient. Connected primitive geometric patches realize a selected CDT weight. A retained orbital construction supplies a joint finite geometry-matter-clock operator and a microscopic encoding of its entire evolution. Each layer has explicit equations and checks; the assumptions connecting the layers are stated where they enter.

The key distinction is between constructing a compatible microscopic realization and showing what phase that realization occupies. A successful inverse construction is a genuine existence result even though its interactions are selected. It need not be unique. The same construction still has to exhibit the desired common light cone, matter interpretation, and gravitational response before it establishes the full physical claim.

Sections 1-13 preserve the foundational derivations and the earlier host/force checkpoint. Sections 14-16 develop the evening advances. Sections 17-19 give the updated result ledger, corrections, and remaining requirements. In particular, the old host uses \(\alpha=11.312\); the new integer-channel construction selects \(\alpha=7\). Results from those ensembles are kept distinct.

The [source catalogue](SOURCES.md) and [derivation companion](DERIVATION_COMPANION.md) retain the afternoon archive. The new sections link directly to the later research reports and their saved calculations in the workspace. Those later files are not silently included in the frozen archive or ZIP. [The update record](EXPLANATION_UPDATE.json) records preservation and delivery checks for this revision.

## 1 What is being derived

The ordinary gravitational branch uses one metric. Capacity strain describes a constrained aspect of that metric relative to a physical clock and boundary prescription. It is not an additional freely propagating gravitational scalar. Persistent matter is retained through renewal; the fast capacity register is refreshed and its previous state is exported to history. A transient marked response, a maintenance cost, and a persistent particle's rest energy have different roles.

This distinction follows the abstract and introduction of the manuscript and its Appendices H, N, O, P, and Q. It prevents several shortcuts that would violate the intended ontology: replacing the physical rest gap by an exclusion cost, counting exported histories as new local capacity states, or treating the capacity coordinate as an independent scalar added to Einstein gravity. [S00](SOURCES.md#s00), [S05](SOURCES.md#s05), [S06](SOURCES.md#s06)

| Manuscript constraint | Role in the continuation |
|---|---|
| H: retained and renewed sectors, marked transfer | Preserve the charged rest gap and coherent retained states through renewal. |
| N: one metric and one matter source | Interpret the static capacity equation as a metric constraint; vary the parent before eliminating fields. |
| O: fixed event measure | Keep physical four-volume counting distinct from host simplex counting and Monte Carlo updates. |
| P: records, relative entropy, visibility costs | Respect the distinction between information cost, entropy change, modular energy, and physical energy. |
| Q: geometry and capacity factors, relational lock | Use separate operator roles within one substrate; do not infer a face-wise metric lock from representation matching alone. |

Three gravitational coefficients must be distinguished throughout:

1. **Reference scale:** in units with the reduced Planck constant and the speed of light equal to one, the manuscript's reference is \(G_*=L_*^2\). In SI units, \(G_*=c^3L_*^2/\hbar\).
2. **Bare or saddle coefficient:** \(G_0\), obtained from the selected angular tensor and physical area calibration.
3. **Interacting response coefficient:** \(G_R\), inferred from an appropriate physical long-distance observable of the same model.

An equality between the first two does not establish an equality with the third. Nor does a correct Gaussian source response determine the interacting phase.

| Symbol | Meaning |
|---|---|
| \(L_*=c\tau_*\) | Electron-calibrated tick length; not automatically a graph bond or simplex edge. |
| \(a\) | Host or regular-tetrahedron edge in the selected calibration. |
| \(v_*\) | Physical four-volume per event in the chain-clock construction. |
| \(A_{\rm ch}\) | Physical area assigned to one effective cut channel. |
| \(m_4\) | Asymptotic four-dimensional longest-chain constant. |
| \(g_{\rm share}\) | Entropy of the complete local capacity/orientation distribution. |
| \(S_\infty\) | Capacity background used in the clock bridge; not \(g_{\rm share}\). |
| \(N\) | Lapse, except where explicitly subscripted as an event or channel count. |
| \(\alpha\) | CDT edge-shape parameter in host formulas; a logarithmic scale variable only in the explicitly named homogeneous calculation. |

## 2 The finite local state and the matter clock

### 2.1 The original capacity ensemble

The local alphabet chooses four distinct labels from a seven-letter set, routes them to four ordered ports, and includes two orientations. Its dimension is

\[
\dim\mathcal H_{\rm cap,o}=\binom74\,4!\,2=1680.
\]

For an unordered four-label set \(s\), the closure value is

\[
K^2(s)=48-\frac{(\sum_{m\in s}m)^2-\sum_{m\in s}m^2}{3}.
\]

It is unchanged by routing and orientation. Write

\[
P_s=\frac{e^{-\eta_*K^2(s)}}{\sum_{s'}e^{-\eta_*K^2(s')}}.
\]

Each of the 48 routing/orientation states over \(s\) has probability \(P_s/48\). The recomputed constants are

\[
\eta_*=0.0298668443935226,\qquad
g_{\rm share}=7.4198000235709.
\]

The specified marked-transfer prescription gives

\[
\epsilon_e=-\frac32 Z_e\log(1-e^{-7g_{\rm share}})
=4.18545879558\times10^{-23},
\qquad Z_e=1.00530828380951.
\]

Here \(\epsilon_e\) is the dimensionless rest gap per proper tick. Its physical rest energy is \(\hbar\epsilon_e/\tau_*\). The clock calibration identifies that energy with the electron rest energy. This is distinct from the much larger maintenance throughput or a local exclusion likelihood. [S06](SOURCES.md#s06), [S15](SOURCES.md#s15)

Faithful full entropy renewal with the prescribed stationary marginal saturates

\[
H(B_{t+1}\mid B_t)=g_{\rm share}-I(B_t;B_{t+1})\leq g_{\rm share}.
\]

Saturation makes the endpoint mutual information vanish and selects the replacement kernel \(K(b,b')=p_*(b')\) within that class. It fixes temporal refresh of the capacity marks. It does not by itself determine spatial event positions or a probability law for geometries.

### 2.2 From causal chains to proper time

The chain-clock argument adds explicit event and cadence premises. Events are distributed uniformly in invariant four-volume, locally as a Poisson process of density \(\rho=1/v_*\). Persistent renewals form causal chains. Between two specified interaction endpoints, the physical cadence is represented by a longest chain. The last condition is variational; it is not a local greedy update algorithm.

For a four-dimensional Minkowski causal diamond of proper duration \(\tau\), using \(c=1\),

\[
V_4(\tau)=\frac{\pi}{24}\tau^4,
\qquad
L_{\rm chain}\sim m_4(\rho V_4)^{1/4}
=m_4\left(\frac{\pi}{24v_*}\right)^{1/4}\tau.
\]

Identifying the asymptotic tick rate with \(1/\tau_*\) gives

\[
\boxed{\frac{v_*}{L_*^4}=\frac{\pi}{24}m_4^4.}
\]

With a gap \(\epsilon_e\) per renewal, the transfer along a trajectory becomes

\[
T_e[\gamma]=\exp\left[-\epsilon_e\int_\gamma\frac{d\tau}{\tau_*}\right].
\]

The Lorentzian action has the corresponding proper-time phase. The same energy defines inertia and the stationary lapse coupling. For a slowly varying static clock, \(d\tau=Ndt\); no independent gravitational charge is introduced.

The original tests checked boost invariance in two dimensions, approach to geodesics in curved two-dimensional examples, and redshift for confined clocks of equal proper width. The unconfined rate calibration requires a defect localization width large compared with the event spacing; a clock confined to only a few event spacings has a different cadence. The construction assumes an invariant-volume event law and a causal geometry. It does not generate the metric from no geometric premises. [S01](SOURCES.md#s01), [S12](SOURCES.md#s12)

The retained value \(m_4=2.35\) is illustrative, based on the earlier finite-size extrapolation. It gives \(v_*/L_*^4=3.9921796827\). The numerical lower estimate near 2.21 is not a rigorous confidence bound on the asymptotic constant. No pending campaign result or newer precise chain-constant measurement is inserted into this consolidation.

### 2.3 Fixed total volume and local event statistics

A fixed total event count can be combined with local Poisson behavior by conditioning the Poisson process on its total count. Given \(N_e\) events in total volume \(N_ev_*\), a region of volume fraction \(f\) has

\[
\mathbb E N_f=N_ef,\qquad
\operatorname{Var}N_f=N_ef(1-f).
\]

Disjoint regional counts have covariance \(-N_ef_1f_2\). Small regions approach the local Poisson law while the total stays fixed. This is a stated event model compatible with the fixed-total-volume premise; memoryless capacity labels alone do not prove it. [S15](SOURCES.md#s15)

## 3 What the normalization problem actually required

### 3.1 Eliminating volume conventions from the blob calculation

The earlier homogeneous volume fit used width \(\widetilde s_0\), kinetic coefficient \(k_1\), effective four-volume \(\widetilde C_4a^4\) per counted \((4,1)\) simplex, and slice duration \(\ell_t\). Under its Einstein minisuperspace interpretation,

\[
G=\frac{\widetilde C_4a^4}{12\pi k_1\ell_t^2},\quad
R^4=\frac{3\widetilde C_4a^4N_{41}}{8\pi^2},\quad
\frac R{\ell_t}=\widetilde s_0N_{41}^{1/4}.
\]

Eliminating the radius and conversion factors yields

\[
\boxed{\frac G{\ell_t^2}=\frac{2\pi\widetilde s_0^4}{9k_1}.}
\]

If \(\widetilde C_4a^4=n_ev_*\), then

\[
\boxed{\frac G{L_*^2}
=\kappa\sqrt{n_e\frac{v_*}{L_*^4}},\qquad
\kappa=\frac{\widetilde s_0^2}{3\sqrt6\,k_1}.}
\]

This eliminated several convention ambiguities. It did not derive \(n_e\), establish that a homogeneous fitted coefficient is the universal gravitational residue, or establish the physical clock used by that ensemble. Those are physical identifications. [S07](SOURCES.md#s07), [S08](SOURCES.md#s08)

Let \(\nu\) instead be the mean number of volume-counting events per spatial tetrahedron per proper tick, and \(T=\ell_t/L_*\). The periodic CDT identity \(N_{41}=2\sum_tN_3(t)\), together with the proposed homogeneous event assignment, gives

\[
n_e=\frac{\nu T}{2},\qquad
T^3=\frac{3(v_*/L_*^4)\nu}{16\pi^2\widetilde s_0^4}.
\]

The combinatorial identity is exact. The identification of a host tetrahedron with a renewing physical object is an additional premise. The same mean ledger says

\[
\frac{V_{\rm site}}{L_*^3}=\nu\frac{v_*}{L_*^4}.
\]

Thus the unknown event rate is equivalently a physical spatial-volume assignment. Simply declaring \(a=L_*\), assigning \(\eta_*\) as an event probability, or choosing a quarter-rate because it makes an old number agree would not derive that assignment. [S09](SOURCES.md#s09)

### 3.2 The paired-cell route

The selected candidate uses one mean event per two-site cell per proper tick:

\[
V_{\rm site}=\frac{v_*}{2L_*}.
\]

A regular-tetrahedron semiclassical calibration then gives

\[
a=(6\sqrt2V_{\rm site})^{1/3},\qquad
A_{\rm ch}=\frac{\sqrt3}{4}a^2.
\]

If the gravitational cut entropy is one bit per channel and the same angular construction supplies the bulk coefficient, the result below will be

\[
G_0=\frac{A_{\rm ch}}{4\ln2}.
\]

Combining the equations gives the explicit scaling

\[
\boxed{\frac{G_0}{G_*}=0.10551926870131369\,m_4^{8/3}.}
\]

At the illustrative input \(m_4=2.35\),

\[
\begin{aligned}
v_*/L_*^4&=3.9921796827,\\
a/L_*&=2.5681207755,\\
A_{\rm ch}/L_*^2&=2.8558245616,\\
G_0/G_*&=1.0300209832.
\end{aligned}
\]

Exact equality with the reference would require \(m_4=2.3240773879\) under these premises. That number is a target implied by the formula, not a measurement or a reason to fix the chain constant to it. [S11](SOURCES.md#s11), [S12](SOURCES.md#s12), [S15](SOURCES.md#s15)

The paired-cell interpretation and regular area-volume relation are still calibration choices. The two-cell geometric code alone does not select them. A volume-state calculation does show that the required additive pair volume lies within the retained operator's spectral range, approximately \([1.71248,4.53199]L_*^3\). A mixed state with mean \(3.99218L_*^3\) exists. Its multiplier was solved to impose that mean; existence is not dynamical selection. [S14](SOURCES.md#s14), [S15](SOURCES.md#s15)

### 3.3 Why the old discrepancy was not removed by this algebra

Using the same calibration in the old public pilot's bulk and cut formulas gives

\[
\frac{G_{\rm bulk}}{G_{\rm cut}}=1.5020714592.
\]

The cell scale and \(m_4\) cancel. Increasing the precision of \(m_4\) cannot change this ratio. Different runs and different measures are not an uncertainty interval for one fixed model.

Changing the physical cell volume also changes the old scalar gradient and source conversion. Under the old scalar conventions,

\[
\frac{G_{\rm scalar}}{G_*}
=\frac{V_p}{\ell^2L_*}\frac{S_0}{S_\infty},
\]

where \(\ell\) is the physical graph bond, not necessarily the tetrahedron edge. Holding \(\ell=L_*\) and \(S_\infty=S_0\) while replacing \(V_p\) by \(v_*/L_*\) gives 3.99218, rather than 1.03002. The later coherent-bond/angular model changes the global state and action rule. It must be tested as that model; old pilot outputs cannot be relabeled as its response. [S12](SOURCES.md#s12)

## 4 Coherent binary bonds inside the original 1680 states

### 4.1 The exact encoding

The routing/orientation factor admits an equivariant decomposition

\[
\mathbb C[S_4]\otimes\mathbb C^2
\cong\mathcal F(\mathbb C^4)\otimes V_{\rm std}.
\]

The four-mode fermionic Fock space has dimension 16; the standard permutation representation has dimension 3. Their product has dimension 48. The equality is stronger than dimension counting. On the five conjugacy classes of \(S_4\), the Fock character is \((16,0,0,4,0)\) and the standard character is \((3,1,-1,0,-1)\). Their product is \((48,0,0,0,0)\), the character of two regular representations.

Consequently,

\[
\boxed{\mathcal H_{\rm cap,o}\cong\mathcal F_4\otimes\mathbb C^{105}.}
\]

The four virtual occupations are encoded observables of existing routing/orientation states. They do not add sixteen new capacity states or redefine the original occupied seven-letter channels. Fermionic signs are necessary for the covariance identity. The saved explicit intertwiner has covariance error about \(1.8\times10^{-14}\). [S15](SOURCES.md#s15)

### 4.2 Preserving the local state while choosing a global vacuum

In the encoding,

\[
\rho_{\rm cell}=\frac{I_{16}}{16}\otimes\sigma,\qquad
\sigma=\bigoplus_{s=1}^{35}\frac{P_s}{3}I_3.
\]

The original full local density matrix is preserved because each routing/orientation block was proportional to the identity. Pair corresponding virtual modes across graph links in the coherent state

\[
|\Omega_\Gamma\rangle
=\prod_{e=(L,R)}\frac{c^\dagger_{L,e}+c^\dagger_{R,e}}{\sqrt2}|0\rangle,
\qquad
\rho_{\Gamma,*}=|\Omega_\Gamma\rangle\langle\Omega_\Gamma|
\otimes\bigotimes_v\sigma_v.
\]

Every cell still has the old marginal. The entropy separates exactly:

\[
g_{\rm share}=4\ln2+S(\sigma)
=2.77258872224+4.64721130133.
\]

A cut through \(N_\partial\) coherent bonds has \(N_\partial\ln2\) of bond entanglement. Independent residual registers contribute volume entropy, not another copy of the same cut modes. The earlier shared-label global ensemble is a different state; its cross-cut information cannot be added to these bonds as though it were a separate register.

The coherence matters. Both the pure bond \((|10\rangle+|01\rangle)/\sqrt2\) and the separable mixture \((|10\rangle\langle10|+|01\rangle\langle01|)/2\) have marginal entropy \(\ln2\). Only the first supplies the claimed entanglement. Fair occupancy alone was insufficient. A concrete bond parent repairs this:

\[
H_e=U(n_L+n_R-1)^2+
t[n_L+n_R-2n_Ln_R-(c_L^\dagger c_R+c_R^\dagger c_L)],
\quad U,t>0.
\]

It has the coherent one-copy bond as its unique ground state, with excitation energies \(U,U,2t\). Choosing this global vacuum is a physical completion; the local Gibbs state alone does not uniquely select it. [S12](SOURCES.md#s12), [S15](SOURCES.md#s15)

### 4.3 Renewal without recording the graph

A joint renewal exports the old capacity state and prepares fresh coherent bonds plus purifications of the residual registers. Its Stinespring map is an isometry. Independent single-cell resets would destroy the bond entanglement.

There is a further issue when geometry is in a superposition. Exporting a graph-dependent old bond vacuum directly multiplies logical coherence by \(\langle\Omega_h|\Omega_g\rangle\). Orthogonal matching vacua would let history distinguish and dephase the graph.

Let \(U_g|\mathrm{ref}\rangle=|\Omega_g\rangle\), and define

\[
D=\sum_g|g\rangle\langle g|\otimes U_g.
\]

Uncompute with \(D^\dagger\), renew in the common reference frame, perform the retained transfer, and prepare the new frame. With the normalized encoding \(J|g\rangle=|g\rangle|\Omega_g\rangle\),

\[
U_{\rm physical}=D(U_{\rm geom}\otimes I)D^\dagger,
\qquad U_{\rm physical}J=JU_{\rm geom}.
\]

This preserves logical geometric coherence while retaining memoryless local capacity renewal. It specifies how to dress a geometric transfer; it does not determine that transfer's amplitudes. [S16](SOURCES.md#s16)

## 5 The angular rule and the bare Einstein coefficient

### 5.1 Why normalized entropy was insufficient

For a fixed cut with \(N_h\) binary channels, consider a central boost contribution \(B_b=bN_hI\). For every \(b\),

\[
Z_{N_h}(\theta)=2^{N_h}e^{-\theta bN_h},\qquad
\rho_{N_h}=\frac{e^{-2\pi B_b}}{Z_{N_h}(2\pi)}=\frac I{2^{N_h}}.
\]

Normalized replicas obey

\[
\frac{Z_{N_h}(2\pi n)}{Z_{N_h}(2\pi)^n}=2^{N_h(1-n)}.
\]

The central coefficient cancels. Thus a trace-one cut state and its entropy do not fix an absolute geometric angular amplitude. The missing input compares angular weights before normalization or relates different area sectors. [S06](SOURCES.md#s06)

### 5.2 One tensor for replicas and curvature

The selected rule is that the unnormalized transfer through one full Euclidean turn equals the half-bond density matrix, with positive continuous angular subdivision:

\[
\boxed{K_h(2\pi)=\rho_h=I_2/2,\qquad
K_h(\theta)=\rho_h^{\theta/(2\pi)}=e^{-b\theta}I_2,
\quad b=\frac{\ln2}{2\pi}.}
\]

This fixes the absolute coefficient that the normalized cut state left free. Around a hinge whose wedge angles sum to \(2\pi-\delta_h\),

\[
\operatorname{Tr}\prod_{w\supset h}K_h(\theta_{hw})
=2e^{-b(2\pi-\delta_h)}=e^{b\delta_h}.
\]

For \(N_h\) channels, \(W_h=e^{bN_h\delta_h}\). The same tensor gives

\[
\operatorname{Tr}K_h(2\pi n)=2^{1-n}=\operatorname{Tr}\rho_h^n.
\]

The cut replica and curvature weight are now two evaluations of one specified tensor, rather than separately normalized objects required to agree. This is the concrete repair. The absolute full-turn rule itself remains selected. [S15](SOURCES.md#s15)

### 5.3 From hinges to the action

On the selected metric continuation, \(A_h=A_{\rm ch}N_h\), and

\[
\log W_{\rm geom}=\frac b{A_{\rm ch}}\sum_hA_h\delta_h.
\]

Using \(\int R\,dV=2\sum_hA_h\delta_h\), the Euclidean action is

\[
I_E=-\frac b{2A_{\rm ch}}\int R\,dV
=-\frac1{16\pi G_0}\int R\,dV,
\qquad
\boxed{G_0=\frac{A_{\rm ch}}{8\pi b}=\frac{A_{\rm ch}}{4\ln2}.}
\]

There is no second independently multiplied Einstein weight. The curvature coefficient is already in the bond contraction. Finite nonlinear edge variations verify the Regge identity

\[
\partial_{\ell_e}\sum_hA_h\delta_h
=\sum_h\delta_h\,\partial_{\ell_e}A_h
\]

on regular and distorted test complexes. The agreement tests the chosen metric action, not the existence of its nonperturbative Einstein phase.

The corresponding open-region boundary normalization is

\[
B_h(\theta)=\rho_h^{-1/2}K_h(\theta)=e^{b(\pi-\theta)}I_2.
\]

Two regions sew with

\[
\operatorname{Tr}[\rho_hB_h(\theta_1)B_h(\theta_2)]
=e^{b(2\pi-\theta_1-\theta_2)}.
\]

Consequently the interior deficit and boundary exterior-angle sums carry the same coefficient. A full turn on each open boundary would double-count the interface reference angle. The finite sewing checks verify this distinction. [S23](SOURCES.md#s23)

### 5.4 Integer channels and metric interpolation

Applying the same sharp binary-area spectrum to both CDT hinge types would require

\[
\frac{\sqrt3}{4}a^2=mA_{\rm ch},\qquad
\frac{\sqrt{4\alpha-1}}4a^2=nA_{\rm ch},\qquad
\alpha=\frac{1+3(n/m)^2}{4}.
\]

The earlier host shape \(\alpha=11.312\) with one spatial channel would require a mixed-hinge count 3.84048608. That branch uses the explicitly stated continuous metric interpolation. Section 14 supplies a separate integer-channel realization at \(\alpha=7\); it does not change the interpretation of the older runs.

Replacing a fluctuating count by its mean is not generally exact:

\[
\log\mathbb E e^{bN_h\delta_h}
=b\overline N_h\delta_h+
\frac{b^2}{2}\operatorname{Var}(N_h)\delta_h^2+\cdots.
\]

Cross-hinge correlations can cancel this quadratic term along particular deficit directions. These observations constrain a microscopic spacetime implementation; they do not supply a universal correction to \(G_R\). [S22](SOURCES.md#s22)

## 6 A primitive geometric parent

The geometric factor of one primitive cell is

\[
\mathcal I_3=\operatorname{Inv}(V_3^{\otimes4}),\qquad\dim\mathcal I_3=7.
\]

It is distinct from the capacity alphabet even though both use seven-dimensional structures. Define gauge-invariant shapes

\[
X=\mathbf J_1\cdot\mathbf J_2,\quad Y=\mathbf J_1\cdot\mathbf J_3,
\quad Z=-12I-X-Y,
\]

and centered operators \(x=X+4I\), \(y=Y+4I\), \(z=Z+4I\), with \(x+y+z=0\). Put \(u=(x,y,z)\), \(B=x^2+y^2+z^2\), and \(Q=i[X,Y]\). For a pair, define

\[
\mathcal D=\sum_ru_r\otimes u_r,\quad
\mathcal E=\sum_r(u_r^2\otimes u_r+u_r\otimes u_r^2),\quad
\mathcal T=\sum_ru_r^2\otimes u_r^2.
\]

The explicit dimensionless parent is

\[
\begin{aligned}
\widehat H_{\rm pair}=\frac1{13^4}\big[&3\,13^4I
+13^2(B\otimes I+I\otimes B-8\mathcal D)\\
&+52\mathcal E+B\otimes B-2\mathcal T-144Q\otimes Q\big].
\end{aligned}
\]

For the four-bundle maximal-fusion map \(T:\mathcal I_3\otimes\mathcal I_3\to\mathcal I_6\), normalize

\[
F=(TT^\dagger)^{-1/2}T.
\]

Exact rational arithmetic establishes

\[
\widehat H_{\rm pair}\geq0,\qquad
\ker\widehat H_{\rm pair}=\operatorname{im}F^\dagger,\qquad
\dim\ker\widehat H_{\rm pair}=13.
\]

There are 36 positive eigenvalues, a dimensionless gap 1.9301241828, and no extra zero modes. Degree four is minimal within the polynomial family searched. Multiplying by a physical energy scale \(J_p\) gives the physical parent; the fusion target does not fix \(J_p\) in tick units. This is an exact inverse construction of an interaction selecting the chosen block. [S13](SOURCES.md#s13)

For a supplied coarse Hamiltonian \(H_c\),

\[
H_f=F^\dagger H_cF+J_p\widehat H_{\rm pair}
\quad\Longrightarrow\quad
Fe^{-itH_f}F^\dagger=e^{-itH_c}.
\]

Thus the selected coarse dynamics can be embedded exactly with a concrete primitive complement. This identity does not derive the dynamics inside the retained sector.

The extension to overlapping identical-port pairs was solved further. On a connected graph of \(n\) cells, the common parent ground space has dimension \(6n+1\), spanned by correlated vectors \(v(z)^{\otimes n}\). A tangent-state variational bound gives a gap no larger than a constant times \(n^{-2}\) on a chain. Such an all-edge parent globally locks shape and cannot by itself be the relativistic propagation Hamiltonian. The working continuation keeps it within primitive blocks and obtains inter-block metric dynamics from the angular curvature action. [S16](SOURCES.md#s16)

## 7 Collective areas and the Einstein saddle

### 7.1 Reconstructing a spatial metric

Measure six coarse directional areas: normals \(e_i\), and normals \((e_i+e_j)/\sqrt2\). These are cuts through a block, not six new faces on one tetrahedron. Let \(r_A=A_A/A_0\). Squared directional areas determine the cofactor matrix

\[
\mathcal C=(\det g)g^{-1},\qquad
\mathcal C_{ii}=r_i^2,\qquad
\mathcal C_{ij}=r_{ij,+}^2-\frac{r_i^2+r_j^2}{2}.
\]

Taking determinants gives \(\det\mathcal C=(\det g)^2\), hence

\[
\boxed{g=\sqrt{\det\mathcal C}\,\mathcal C^{-1},\qquad
\sqrt{\det g}=(\det\mathcal C)^{1/4}.}
\]

This is an exact algebraic reconstruction on the domain \(\mathcal C>0\). Arbitrary six counts need not lie on that domain. A microscopic realization must preserve metricity and compatible gluing between blocks. The physical interpretation of these coarse cut counts is part of the selected continuation. [S17](SOURCES.md#s17)

### 7.2 The metric Hessian and physical waves

The angular Regge action was expanded on an infinite four-dimensional Kuhn triangulation with 24 simplices and 15 edge classes per translation cell. On the flat background, the Schlaefli identity gives the local Hessian of \(-\sum A\delta\) as \(J_A^TJ_\theta\). Bloch assembly produces \(H_\ell(p)\), whose vertex-displacement gauge vectors obey

\[
H_\ell(p)G(p)=0,\qquad
G_{e\mu}=\frac{d_{e\mu}}{\ell_e}(e^{ip\cdot d_e}-1).
\]

Five nonmetric edge directions are eliminated by saddle equations. This is a Schur complement, not a claim that an indefinite Euclidean Gaussian integral converges. The ten metric components then approach the Fierz-Pauli quadratic form, with the coefficient inherited from \(G_0\).

At nonzero Euclidean momentum there are four gauge zeros, five positive directions, and one negative conformal direction. These off-shell counts are not physical polarization counts. The Lorentzian field equations on the null cone have six solutions modulo four gauge directions, leaving the two transverse traceless polarizations. Their reduced action is

\[
S_{\rm TT}=\frac1{64\pi G_0}\int d^4x
\left[(\dot h_{ij}^{\rm TT})^2-(\nabla h_{ij}^{\rm TT})^2\right].
\]

The saved calculations check two sheared regulator backgrounds and small momenta; tensor errors decrease quadratically. This establishes the selected metric saddle's continuum wave structure. It does not prove that the interacting discrete ensemble occupies that phase. [S16](SOURCES.md#s16)

### 7.3 The tree-level source calculation

The same proper-length source has Euclidean linear coupling \(\frac12\int T_{\mu\nu}h_{\mu\nu}\). For a static density \(T_{44}=\rho\), solving the gauge-singular Hessian on conserved sources gives

\[
h_{44}(k)=-\frac{8\pi G_0\rho(k)}{k^2},\qquad
\Phi(k)=\frac12h_{44}(k).
\]

Therefore

\[
\nabla^2\Phi=4\pi G_0\rho,\qquad
\Phi(r)=-\frac{G_0M}{r}
\]

for the isolated point-source boundary problem. The numerical extraction

\[
G_{\rm static}=-\frac{k^2h_{44}}{8\pi\rho}
\]

approaches the bond value; the reported two-momentum extrapolation agrees to better than \(10^{-7}\) relatively on both backgrounds. This is a source-response calculation with an independently fixed source normalization within the selected saddle. Its coefficient is not retuned. It is a tree-level consistency result, not an interacting measurement of \(G_R\). [S16](SOURCES.md#s16)

## 8 Reconnection amplitudes and quantum constraints

### 8.1 From binary switches to count motion

For \(M\) binary reconnection switches, the normalized symmetric count state \(|n\rangle\) is a superposition of \(\binom Mn\) patterns. A microscopic raising sum obeys

\[
S^+|n\rangle=\sqrt{(n+1)(M-n)}\,|n+1\rangle.
\]

Independent constant-rate flips therefore do not yield a flat massless count coordinate. Their multiplicity produces a binomial distribution and a gap. A selected count measure requires a corresponding diagonal correction. A normalized shift

\[
\mathsf T^+=S^+[(n+1)(M-n)]^{-1/2}
\]

acts as a unit count shift in the interior. Products of these shifts implement paired reconnections. This keeps the microscopic patterns rather than replacing each orbit by one arbitrary representative. [S17](SOURCES.md#s17)

For \(q_A=r_A-1\), let \(J_{aA}=\partial g_a/\partial q_A\) in an orthonormal symmetric-matrix basis. The metric DeWitt tensor is

\[
D^{ab}(g)=\frac{\operatorname{tr}(E_agE_bg)
-\tfrac12\operatorname{tr}(gE_a)\operatorname{tr}(gE_b)}{\sqrt{\det g}}.
\]

Canonical momentum transformation gives the count mobility

\[
\boxed{K(q)=J^{-1}D(g(q))J^{-T}.}
\]

The selected nonlinear Hamiltonian contains

\[
H_K=\frac{16\pi G_0}{V_{\rm ref}}p_q^TK(q)p_q,
\qquad
H_R=-\frac{V_{\rm ref}}{16\pi G_0}\sqrt{\det g}\,R[g].
\]

The mixed entries require correlated reconnections. Assigning their amplitudes from this mobility is an inverse completion from the metric action. The local capacity Gibbs weights do not force those amplitudes.

The nonlinear classical check reproduces Kasner evolution with exponents \((-1/3,2/3,2/3)\), with maximum relative metric error about \(2.45\times10^{-11}\) on the tested interval. Freezing the mobility gives about 7.95 percent velocity error. This distinguishes the nonlinear construction from a free theory in relabeled coordinates. [S17](SOURCES.md#s17)

### 8.2 Measure and ordering

The exact area Jacobian and DeWitt determinant give

\[
\det D=-\frac12\det g,\qquad
|\det J|=64\sqrt2\frac{\prod_A r_A}{\det\mathcal C},
\]

and therefore, up to an irrelevant overall constant,

\[
\boxed{\mu(q)=\frac{\prod_A r_A}{(\det\mathcal C)^{5/4}}.}
\]

A scalar wavefunction in \(L^2(\mu\,dq)\) becomes the half-density \(\psi=\sqrt\mu\,\phi\) in the orthonormal count basis. This is a kinematic measure induced by the selected kinetic tensor, not yet a physical state measure or a probability distribution over triangulations.

The chosen ordering is Weyl ordering in metric components, transported unitarily into area coordinates. With \(c_K=16\pi G_0/V_{\rm ref}\), it gives

\[
\boxed{H_{W,\rm count}=H_{{\rm LB},\rm count}
-c_K\frac{21}{16\sqrt{\det g}}.}
\]

The rational correction was checked symbolically and numerically. It is an ordering term, proportional to \(\hbar^2\) with units restored, and not an independently fitted cosmological constant. Another ordering would be a different completion. [S18](SOURCES.md#s18)

### 8.3 What closes and what only converges

The local staggered Gaussian construction obeys exact identities \(CG=0\), \(LG=0\), and \(C(2K)=-DG^\dagger\). These preserve the linearized scalar and vector constraints. Within the tested kinetic ansatz the trace coefficient is forced to \(1/2\). The physical nonzero-momentum dispersion has two modes with

\[
\omega^2=\frac4{a_B^2}\sum_i\sin^2(k_i/2),
\]

without additional zeros at lattice corners. A finite prime-field code supplies a separate exact algebraic example; it is not identified with the 13-state intertwiner block.

For continuous metric coordinates at a fixed spatial regulator, the chosen Weyl commutators equal the Weyl quantization of the regulated classical brackets on a suitable interior test domain. The reason is polynomial degree: local kinetic terms are quadratic in momenta, the potential has no momenta, and the spatial generator is bilinear. Higher Moyal terms vanish in these brackets. This does not make a defective regulated classical algebra first class.

Finite count shifts introduce an additional error. On the fixed three-cell smooth probe, the quantum-current discrepancy decreases from 1.04584 percent at reference count 100 to 0.0163828 percent at count 800, with second-order convergence. A later comparison of that three-cell spatial regulator against the actual spatial Lie derivative gives 8.5389 percent. These are different errors. The 0.016 percent number is not a full quantum-gravity closure accuracy.

Separate smooth spatial tests converge toward the expected deformation law as the spatial grid is refined. None establishes a common physical state space, positive inner product, and regulator-independent interacting limit. A small reflecting count box has no exact zero of the selected Weyl constraint. A homogeneous scale/shape construction does provide a positive spectral rigging form above its stated threshold, but solves only the homogeneous scalar-constraint problem. [S17](SOURCES.md#s17), [S18](SOURCES.md#s18), [S19](SOURCES.md#s19), [S24](SOURCES.md#s24)

## 9 Histories and the conformal sector

### 9.1 The finite history sum is explicit

The finite Hermitian reconnection matrix defines \(e^{-\beta H}\) and its ordered jump expansion. A path stays in each state with the diagonal exponential and receives a factor \(-H_{yx}\) at each jump. A closed three-jump product is invariant under diagonal rephasing because all phases telescope.

The saved 729-state calculation contains a triangle with product \(-0.254534167364\) in its stated energy units. Thus a positive bond curvature contraction does not imply that all reconnection histories have positive weights. Discarding signs changes the Hamiltonian.

Exact finite time blocking produces a positive benchmark and a Monte Carlo response agreeing with spectral evaluation. It validates response measurement in that finite system. Exact interval summation grows too rapidly to be the large spatial force solver. [S20](SOURCES.md#s20)

### 9.2 Isolating scale does not remove every stencil sign

Let \(v=\sqrt{\det g}\) and \(r_A=1+q_A\). The count kinetic tensor separates exactly as

\[
K_{\rm conf}=-\frac{rr^T}{6v},\qquad
K_{\rm shape}=K+\frac{rr^T}{6v}.
\]

The shape tensor is positive semidefinite with rank five. The unique negative continuum direction is the overall scale. But the chosen finite stencil still has nine negative elementary triangles after removing that direction. A positive continuum symbol can be represented by a non-monotone stencil. A sign flip of the scale term within the old stencil even creates a spurious ultraviolet negative mode. Thus not every negative loop can be attributed to the conformal instability. [S21](SOURCES.md#s21)

### 9.3 Static sources require the constrained fields

A Gaussian contour rotation must rotate the source and observable along with the negative mode. If \(h=Ry\), the relevant covariance is

\[
\langle hh^T\rangle=R|\lambda|^{-1}R^T=K^{-1},
\]

with a transpose, not a Hermitian conjugate. In the checked static example the correct prescription gives \(G/G_0=1\). Dropping the negative direction gives \(4/3\); using its absolute eigenvalue with an unrotated source gives \(5/3\); retaining only the two spatial wave polarizations gives zero.

The last result explains why a positive wave-sector sampler with a static density source was insufficient. A static Newton field is carried by constrained non-wave components. They can be integrated out, but their induced source action must remain. The positive free-wave Monte Carlo checks its input Gaussian covariance; it does not measure interacting renormalization. [S21](SOURCES.md#s21)

### 9.4 Exact conditional integration of the scale factor

For \(g_{\mu\nu}=\Omega^2\widehat g_{\mu\nu}\), at zero cosmological constant and with the appropriate boundary treatment,

\[
S_E=-c_R\int\sqrt{\widehat g}
[\Omega^2\widehat R+6(\widehat\nabla\Omega)^2],
\qquad c_R=\frac1{16\pi G_0}.
\]

A prescribed proper-length probe contributes \(\int\sqrt{\widehat g}\,j\Omega\). Fix the mean scale, set \(\Omega=1+i\chi\) with zero-mean real \(\chi\), and let \(P\) project out the constant mode. Define

\[
A=P(-6\widehat\Delta+\widehat R)P,
\qquad \eta=P(j-2c_R\widehat R).
\]

If \(A>0\) and the contour measure is flat \(D\Omega\), Gaussian integration gives

\[
\begin{aligned}
S_{\rm eff}[\widehat g,j]={}&-c_R\int\sqrt{\widehat g}\,\widehat R
+\int\sqrt{\widehat g}\,j\\
&+\frac1{4c_R}\langle\eta,A^{-1}\eta\rangle
+\frac12\log\det A,
\end{aligned}
\]

up to specified shape-independent factors at fixed mode count. This is a real positive conditional weight after removing a common contour phase. It retains a nonlocal curvature/source interaction and a determinant; freezing the scale would lose them.

Its conditions matter. A cosmological or fixed-four-volume term introduces \(\Omega^4\), the restricted operator is not positive on every shape, and flat contour measure has not been derived for the finite count histories. The original counterexample \(\langle(1+i\chi)^8\rangle<0\) at a particular Gaussian variance disproves a proposed measure insertion, not positivity of every possible complete theory. [S21](SOURCES.md#s21)

### 9.5 A coordinate density is not a new history weight

For a finite transfer \(T\) in an orthonormal count basis, the scalar kernel is

\[
K(x,y)=\frac{T(x,y)}{\sqrt{\mu(x)\mu(y)}}.
\]

For a closed path,

\[
\boxed{\prod_i\mu(x_i)\prod_iK(x_i,x_{i+1})
=\prod_iT(x_i,x_{i+1}).}
\]

The density cancels against neighboring kernel factors. Inserting another \(\mu\) into the normalized count transfer changes the model. Conversely, this identity does not prove a flat continuum conformal measure after momentum integration, constraints, gauge fixing, and ordering. The actual remaining problem is matching the full kernel and boundary sector to a geometric history sum. [S22](SOURCES.md#s22)

## 10 A proper-clock time step

Assume a positive bounded lapse on the retained domain,

\[
N=\sqrt{I-s/S_\infty},\qquad
0<N_{\min}I\leq N\leq N_{\max}I.
\]

For the specified Hermitian count generator \(H_0\), choose

\[
H_N=N^{1/2}H_0N^{1/2},\qquad
\mathbb H=H_N+NP_\tau+jB,
\quad B=N^{1/2}(V/V_{\rm ref})N^{1/2}.
\]

The ideal clock \(P_\tau=-i\partial_\tau\) is an auxiliary completion, not a finite marked carrier already derived from the ontology. In clock-momentum sector \(p\),

\[
U_t(p,j)=e^{-it(H_N+pN+jB)}.
\]

Differentiating this same operator gives the elapsed-clock response

\[
\mathcal T_t=iU_t^\dagger\partial_pU_t\big|_0
=\int_0^tdu\,U_u^\dagger NU_u,
\]

and the composition law

\[
\mathcal T_{t+s}=\mathcal T_s+U_s^\dagger\mathcal T_tU_s.
\]

When lapse and geometry do not commute, replacing the entire clock history by \(tN\) or by an exponential of its first response discards unequal-time commutators.

For a reference-energy component,

\[
(H_N-iN\partial_\tau)\Psi=E\Psi.
\]

The positive clock flux is \(\Psi^\dagger N\Psi\). Set \(\chi=N^{1/2}\Psi\); then

\[
\boxed{i\partial_\tau\chi=(H_0-EN^{-1})\chi,
\qquad V_E(\tau_*)=e^{-i\tau_*(H_0-EN^{-1})}.}
\]

This is a unitary proper-clock step on the stated domain. The scalar transfer \(A_E=N^{-1/2}V_EN^{1/2}\) satisfies \(A_E^\dagger NA_E=N\). Combining it with moving-frame renewal gives

\[
\mathbb V_E=D_{\rm out}(I\otimes W_*)
(V_E\otimes I_{\rm cap})D_{\rm in}^\dagger,
\qquad \mathbb V_E^\dagger\mathbb V_E=I.
\]

In this auxiliary-clock construction, renewal was attached to proper-clock boundaries. Numerical subdivisions are not additional physical resets. The later native-matter analysis in Section 15 makes a necessary distinction: background local renewal must not become a particle-path-controlled erasure schedule, since such records can destroy interference. [S23](SOURCES.md#s23)

A turning point of spatial volume does not necessarily stop this clock. The checked expanding, contracting, and superposed volume states all retain positive clock response. At zero lapse the inverse-lapse clock representation fails, while the underlying finite reference-time evolution can remain unitary.

Many local clocks pose a separate condition. Neighboring normal deformations need not commute literally; in GR their difference is a spatial deformation:

\[
[H[N],H[M]]=iD[\beta],\qquad
\beta^i=g^{ij}(N\partial_jM-M\partial_jN).
\]

The remaining error must be assessed after subtracting that expected displacement. Exact exponentiation cannot remove an algebra residual. The one-clock construction therefore does not by itself establish quantum refoliation invariance or a native many-clock transfer. [S24](SOURCES.md#s24)

## 11 The earlier selected covariant history model

### 11.1 Defining the host

The covariant route adopts the G3 geometric counting prescription: count compatible causal triangulations with the required relabeling quotient and no unlisted geometry weight. For boundaries \(g_0,g_1\),

\[
T(g_1,g_0;z_{41},z_{32})
=\sum_{[\mathcal T]\in\mathcal C(g_1,g_0)}
\frac{z_{41}^{N_{41}}z_{32}^{N_{32}}}{C(\mathcal T)}W_g(\mathcal T).
\]

The domain has adjacent integer slices and the usual causal simplex types. \(W_g\) is the angular curvature weight, including boundary angles. Fugacities or fixed coefficients specify volume treatment. Uniform event placement inside a geometry does not imply uniform counting over geometries; G3 is an explicit host choice.

Boundary symmetry factors give

\[
T^{(2)}(g_2,g_0)=\sum_{g_1}C(g_1)T(g_2,g_1)T(g_1,g_0).
\]

The orthonormal kernel is \(\widetilde T(g',g)=\sqrt{C(g')C(g)}T(g',g)\). At a finite symmetric cutoff it is real symmetric, so its square is positive semidefinite. This does not prove every one-step eigenvalue is positive or establish a continuum Lorentz-invariant theory.

The capacity encoding attaches algebraically as

\[
T_{\rm enc}=J\widetilde TJ^\dagger,\qquad
T_{\rm enc}^n=J\widetilde T^nJ^\dagger.
\]

It does not import a second shared-label partition factor. A Monte Carlo sequence of local moves is an algorithm for sampling complexes; it is not an additional physical history multiplicity. [S25](SOURCES.md#s25)

The first exact diagnostic sums 1,920 genuine causal slab triangulations: 120 boundary-marked staircase histories and their 1,800 distinct one-move neighbors. It checks geometric and sourced boundary sewing. This is a finite restricted family, not an exhaustive triangulation ensemble. Its positive unconditioned probe covariance is dominated by changing total volume; the fixed-composition component has the opposite sign. A single coarse separation and slab cannot decide a Newton force.

The earlier gapped canonical trial ground state is a diagnostic of that trial state and source, not a prerequisite the selected covariant branch must solve before it can be tested. Conversely, choosing this covariant branch does not prove it is exactly the finite canonical reconnection kernel in another representation. The signed-loop obstruction rules out the simplest entrywise-positive identification in the same basis. [S24](SOURCES.md#s24), [S25](SOURCES.md#s25)

### 11.2 Couplings and the host clock

The paired-cell calibration gives the exact dimensionless relation

\[
\frac{a^2}{G_0}=\frac{16\ln2}{\sqrt3}=6.40301938055.
\]

At retained shape \(\alpha=11.312\), the curvature map is

\[
(\kappa_0,\Delta,\kappa_4^{\rm curv})
=(2.70257004,0.43691236,-0.42026496),
\]

with

\[
S_E=-(\kappa_0+6\Delta)N_0
+(\kappa_4+2\Delta)N_{41}+(\kappa_4+\Delta)N_{32}.
\]

Changing \(m_4\) scales \(a\) and \(G_0\) together and leaves their ratio fixed. It does not automatically preserve a separately chosen volume ensemble or prove that existing campaigns test this model.

The Lorentzian and Euclidean four-simplex volumes differ:

\[
v_{41}^{L,E}=\frac{\sqrt{8\alpha\mathbin{\pm}3}}{96},\qquad
v_{32}^{L,E}=\frac{\sqrt{12\alpha\mathbin{\pm}7}}{96}.
\]

Here the plus sign is Lorentzian and physical volume is \(a^4v\). With a trapezoidal spatial-volume convention and \(r=N_{32}^{\rm slab}/N_{41}^{\rm slab}\), the volume-equivalent lapse is

\[
\frac{\tau_{\rm vol}^{L,E}}{L_*}
=\frac{a/L_*}{4\sqrt2}
\left[\sqrt{8\alpha\mathbin{\pm}3}
+r\sqrt{12\alpha\mathbin{\pm}7}\right].
\]

It is a coarse volume-to-duration dictionary, not automatically a marked matter clock or a local geodesic duration. At the retained input,

\[
\tau_{\rm vol}^L/L_*=4.38972153+5.42399632r.
\]

A host interval is therefore not silently one tick. Physical-volume weighting, \(N_{41}\) weighting, and total-simplex weighting also differ when composition fluctuates. Matching only \(\kappa_0\) and \(\Delta\) is not a full ensemble equivalence. [S22](SOURCES.md#s22)

## 12 The nonlinear capacity equation and its meaning

The static completion is useful independently of the quantum-history route because it makes the capacity observable precise within the selected Einstein branch.

Write

\[
ds^2=-N^2c^2dt^2+h_{ij}dx^idx^j,\qquad N\to1
\]

at the reference boundary. The clock capacity is

\[
q_\tau=N^2,\qquad s_\tau=S_\infty(1-N^2).
\]

In spherical symmetry the radial quantity

\[
q_R=(\nabla R)^2=1-\frac{2Gm(R)}{c^2R}
\]

is another observable of the same metric. They agree in the appropriately normalized connected static spherical vacuum exterior, but not throughout matter. Inside a supported spherical shell, \(q_R=1\) while \(q_\tau<1\) relative to infinity. The interior is locally flat and force-free. Thus no local curvature scalar alone recovers that boundary-relative clock deficit.

For static spherical matter,

\[
\frac{d}{dr}\log\frac{q_\tau}{q_R}
=\frac{8\pi Gr}{c^2q_R}\left(\rho+\frac{p_r}{c^2}\right).
\]

The clock therefore depends on exterior redshift information as well as enclosed mass. This correction adds no new gravitational degree of freedom. [S05](SOURCES.md#s05)

For general static configurations, let \(\mathcal E=T_{\mu\nu}n^\mu n^\nu\) and \(\mathcal S=h^{\mu\nu}T_{\mu\nu}\), both in energy-density units. Varying the parent before eliminating constraints gives, at zero cosmological constant,

\[
D^2N=\frac{4\pi G}{c^4}N(\mathcal E+\mathcal S).
\]

Since \(D^2N^2=2ND^2N+2|DN|^2\),

\[
\boxed{D^2q_\tau=\frac{8\pi G}{c^4}q_\tau(\mathcal E+\mathcal S)
+\frac{|Dq_\tau|^2}{2q_\tau}.}
\]

Equivalently,

\[
\boxed{D^2s_\tau
=-\frac{8\pi GS_\infty}{c^4}
\left(1-\frac{s_\tau}{S_\infty}\right)(\mathcal E+\mathcal S)
-\frac{|Ds_\tau|^2}{2(S_\infty-s_\tau)}.}
\]

In the weak nonrelativistic limit this becomes \(\nabla^2s_\tau=-8\pi GS_\infty\rho/c^2\), with \(s_\tau=-2S_\infty\Phi/c^2+\cdots\). The source includes spatial stress as well as energy in the full static equation. The remaining metric equations and matter equilibrium must still be satisfied. This one lapse equation is not all of GR.

The same proper-time matter energy fixes the static coefficients

\[
\kappa_{\rm phys}=\frac{c^2}{2S_\infty},\qquad
\gamma_{\rm phys}=\frac{c^4}{16\pi GS_\infty^2}.
\]

These do not independently determine \(G\); they show how source and stiffness must be converted consistently. [S05](SOURCES.md#s05), [S06](SOURCES.md#s06)

There is also a dynamical lapse identity. With \(c=1\), \(K_{ij}=-\tfrac12\mathcal L_nh_{ij}\), and shift \(\beta\),

\[
\begin{aligned}
D^2q_N={}&2q_N[K_{ij}K^{ij}+4\pi G(\mathcal E+\mathcal S)-\Lambda]\\
&-2N(\partial_t-\mathcal L_\beta)K
+\frac{|Dq_N|^2}{2q_N}.
\end{aligned}
\]

This follows from the ADM trace evolution equation. It extends the constrained mathematics, but \(q_N=N^2\) depends on the clock and slicing. Even maximal slicing admits inequivalent lapse profiles on the same spacetime. A general physical capacity observable still needs its relational clock, region, and boundary prescription.

Relative entropy alone cannot supply the missing linear observable. For a faithful reference state,

\[
D(\rho\Vert\rho_0)=\Delta\langle-\log\rho_0\rangle-\Delta S,
\]

and a smooth normalized perturbation has \(D=O(\varepsilon^2)\). A differentiable function of \(D\) alone therefore lacks the generic linear response to a weak source. Modular energy and the physical regional algebra contain information that this scalar discards. [S06](SOURCES.md#s06)

## 13 The force measurement

### 13.1 The observable

For mass-independent prepared source trajectories on each geometry, let their Euclidean proper lengths be \(L_1,L_2\). Define

\[
W_i=e^{-m_iL_i},\qquad
R=\frac{\langle W_1W_2\rangle}
{\langle W_1\rangle\langle W_2\rangle}.
\]

The ratio removes the two isolated-source terms. The mixed derivative at zero mass is

\[
\left.\partial_{m_1}\partial_{m_2}\log R\right|_0
=\operatorname{Cov}(L_1,L_2).
\]

For a sufficiently stationary long-duration preparation, the interaction-energy coefficient is therefore

\[
\boxed{Q(r,T)=-\frac{\operatorname{Cov}(L_1,L_2)}{T}.}
\]

Attraction in an Einstein long-distance regime would give \(Q\to-G_R/r\). Fixing \(L_1\) separately on every geometry would make the covariance vanish and remove the desired response. The denominator in the current diagnostic is an ensemble clock average, not a geometry-by-geometry fixed first length.

Conditionally on the Einstein Gaussian propagator, the finite-duration benchmark is

\[
Q(r,T)=-\frac{2G}{\pi r}
\left[\arctan(T/r)-\frac{r}{2T}\log(1+T^2/r^2)\right],
\]

which tends to \(-G/r\). It is a normalization check for a specified propagator, not a derivation of the interacting G3 propagator. [S27](SOURCES.md#s27), [S28](SOURCES.md#s28)

### 13.2 Holding separation on a fluctuating geometry

Coordinate positions or identical timelike edges do not define a fluctuating, physically held pair. The first attempt used a harmonic coordinate construction. Only a fraction of the attempted pairs passed both causal-path and separation checks; there was no fixed-source preparation valid on the whole saved ensemble. Curves conditioned on valid sources were debug outputs, not unconditional force estimates.

The repair works intrinsically. Within each simplex, the signed edge lengths determine the Lorentzian metric on barycentric tangent vectors. Intrinsic face isometries transport the first source and its frame. Spatial separation is computed in the induced slice metric. A corridor problem minimizes a sum of physical segment norms through convex face contacts.

If separation is \(D\), its endpoint rate is

\[
\dot D=A_D+e\cdot v.
\]

Here \(A_D\) includes the changing metric, first source, and moving cut faces; \(e\) is the unit spatial endpoint gradient. Among velocities enforcing \(\dot D=0\), the minimum-norm choice is

\[
v_{\min}=-A_De,\qquad U_2=U_\perp-A_De.
\]

Its timelike condition is \(-N^2+A_D^2<0\). The implementation checks actual connecting segments and halves failed steps. Nonunique path contacts require a selected branch; no theorem of global continuation across every geometry has been proved. [S27](SOURCES.md#s27)

A minimum inside one chosen corridor need not be the global distance. The repair therefore pairs an explicit path upper bound with a global lower bound. Any continuous slice field satisfying \(|\nabla f|\leq1\) obeys

\[
f(q)-f(p)\leq d(p,q).
\]

A conforming finite-element field supplies such a lower bound after independent physical-gradient rescaling. Refining that field improves the certificate without changing the physical triangulation. The optimizer's objective alone is not treated as a physical upper bound. These are numerical feasibility checks, not interval-arithmetic proofs.

The principal four-interval trajectory shows time-step convergence and passes the separation criterion at all 403 checked initial, endpoint, and midpoint locations in the revised audit. This is a sampled trajectory certificate, not a bound on the continuous supremum or evidence of whole-ensemble coverage.

### 13.3 Source normalization and boundary preparation

Use a normalized initial mark distribution \(\mu_g\) on each geometry and leave final marks unobserved:

\[
Z_{m_1m_2}=\sum_gP_0(g)\int\mu_g(dX_0)
e^{-m_1L_1-m_2L_2}.
\]

When the source is defined on all of the support, \(Z_{00}=1\). A deterministic source transport is a normalized delta kernel; its coordinate Jacobian is not an extra geometry weight. The source is an external measuring preparation, not a derived native matter path measure.

Rejecting geometries because source construction failed would change the geometry distribution. The active measurement instead retains all forty inputs at equal weight and suppresses a requested response if source coverage is incomplete. Mixing different initial marks also introduces a within-mark covariance contribution; that must not silently be interpreted as gravitational ensemble response. [S27](SOURCES.md#s27), [S28](SOURCES.md#s28)

### 13.4 The frozen afternoon experiment checkpoint

The force diagnostic uses fresh saved geometries from the selected action and G3 counting, with a predeclared hard Lorentzian four-volume window of approximately two percent and no added volume fugacity. It uses none of the sealed native campaign outputs.

The archived afternoon checkpoint has three of forty primary geometries complete. This historical snapshot is preserved here; the explanation update does not refresh live worker data or analyze new campaign outputs. The primary radii are \(r/a=0.3,0.5,0.7\), with one-, two-, and four-interval windows beginning at host time 0.137. The original \(0.9a\) test is unresolved and retained separately. This amendment was made on source-validity grounds before obtaining an ensemble force curve. All requested primary geometries are still required.

With \(A=L_1/a\), \(B=L_2/a\), and \(\tau=\langle A\rangle\), the code reports

\[
q(r)=Q(r)/a=-\frac{\operatorname{Cov}(A,B(r))}{\tau},
\]

and the paired finite-difference force

\[
\frac{F_{[r_1,r_2]}}{m_1m_2}
=-\frac{q(r_2)-q(r_1)}{(r_2-r_1)/a}.
\]

It also checks finite masses, block-bootstrap sensitivity, and first-half versus second-half response. The estimator passes an independent exact two-state test, including the force sign and suppression of incomplete ensembles. That validates the estimator, not the physical model.

The saved chain is short and drifting, with roughly five effective samples in the earlier action diagnostic. The separations are below one host edge, so there is no resolved interval \(a\ll r\ll L_{\rm box}\). Even a completed result from this batch is a finite-box, finite-duration diagnostic. A reliable infrared \(G_R\) additionally requires equilibrated ensembles, a suitable distance window, duration stability, and calibrated observables.

The worker was confirmed running before this archive was made. It checkpoints after each radius and is programmed to stop on three consecutive unresolved geometries or an unexpected error; the source work budget is checked at audit boundaries. It was not altered or restarted for this consolidation. The archived progress is historical, not a live monitor. [S28](SOURCES.md#s28)

## 14 Connected primitive geometry that reproduces the selected CDT weight

The evening construction makes the geometric interface concrete. The earlier abstract embedding is now implemented by connected networks of the original spin-three geometric cells. Their normalized contractions reproduce the selected Euclidean CDT curvature weight. This is an existence construction: its interactions are specified explicitly and checked. Uniqueness is not needed for that result. The physical phase of those interactions is a separate question. The full derivation and matrices are in [the connected construction report](../Matter%20sector/chain_clock_2026-10-13/causal_primitive_realization_2026-10-16/CONNECTED_CDT_CONSTRUCTION.md).

### 14.1 Integer channels select a new regulator branch

For spatial edge length \(a\) and Euclidean mixed edge length \(\sqrt\alpha a\), the two triangle areas are

\[
A_{\rm SL}=\frac{\sqrt3}{4}a^2,\qquad
A_{\rm mixed}=\frac{\sqrt{4\alpha-1}}4a^2.
\]

Assign one channel to a spatial triangle and three to a mixed triangle. Their area ratio is three, so \(4\alpha-1=27\) and \(\alpha=7\). The same provisional \(m_4=2.35\) gives

\[
a=2.56812077553L_*,\qquad
A_{\rm ch}=2.85582456165L_*^2,\qquad
G_0=1.03002098319G_*.
\]

The new choice solves the displayed integer Euclidean channel mismatch for this branch. It does not change the older \(\alpha=11.312\) runs. Nor does it independently remeasure the chain constant or Newton's constant.

The needed coarse tetrahedral intertwiner spaces are \(\operatorname{Inv}(3,3,3,3)\), \(\operatorname{Inv}(3,9,9,9)\), and \(\operatorname{Inv}(9,9,9,9)\), with dimensions seven, seven, and nineteen. Spin nine is the maximal fusion of three original spin-three facets. A four-cell chain reaches the full seven-dimensional mixed space while keeping two thirteen-state paired sectors. A six-cell cycle reaches the full nineteen-dimensional space while keeping three paired sectors. The numerical ranks and independent contraction checks are recorded in the source report.

These are connected spin-network patches. A literal finer tetrahedral ball with four connected geometric face disks is a stronger condition. The tested six- and eight-tetrahedron balls reach only rank thirteen. The full-rank cycle has not been shown to be such a ball. This matters only if the microscopic graph is also required to be that particular fine metric triangulation.

### 14.2 Matrix normalization fixes the microscopic measure

Let \(R_e\) be either surjective raw patch map. Define

\[
F_e=(R_eR_e^\dagger)^{-1/2}R_e,\qquad
I_e=F_e^\dagger,\qquad I_e^\dagger I_e=I.
\]

This is a complete matrix normalization, including the shape dependence. It is more restrictive than adjusting an overall coupling. For a normalized coarse shape packet \(u_e\), its microscopic image \(I_eu_e\) has norm one. An additional positive block parent \(\Delta(P_{\rm pair}-P_{\rm code})\) selects this code inside the retained paired ground space. Its support is a fixed finite patch.

At each four-simplex choose the product of its boundary packets multiplied by the angular weight

\[
w_\sigma=\exp\left[-b\sum_{h\subset\sigma}N_h\theta_{h\sigma}
-\lambda V_\sigma\right],\qquad b=\frac{\ln2}{2\pi}.
\]

Interior packet contractions give one. The existing full-turn and boundary half-turn factors then give

\[
W(T)=\exp\left[
b\sum_{h\in\mathrm{int}}N_h\delta_h
+b\sum_{h\in\partial}N_h\psi_h
-\lambda\sum_\sigma V_\sigma\right].
\]

With \(A_h=A_{\rm ch}N_h\), this is the selected Regge weight with curvature coefficient \(1/(8\pi G_0)\). The factorization proves the identity for arbitrary allowed history size. A check on 1,920 causal slabs has maximum log-weight error \(1.46\times10^{-13}\); external scalar source and boundary-sewing checks agree at comparable precision.

Raw, unnormalized contractions would multiply each internal tetrahedron by a shape-dependent norm. Those factors change the ensemble. The normalization above removes them exactly within the selected construction. This explains how a microscopic measure can be made to match the chosen coarse measure. It does not establish that the original unmodified interaction already produced it, or explain the registered P3 discrepancy after the fact.

The geometric observables here are transported coarse operators. Equality to sums of unmodified fine volume operators is not established. The construction is Euclidean; an operator-level Lorentzian representation lift remains distinct from assigning Lorentzian edge lengths to the coarse simplices.

### 14.3 Which simulation would test this branch

The new curvature-only couplings are \(\kappa_0=2.20205311516\), \(\Delta_{\rm CDT}=0.326138328034\), and \(\kappa_4=-0.304774619960\). The last is not a tuned grand-canonical critical coupling. Volume control and any physical volume term must still be specified.

The normalized internal geometric factors can be contracted analytically, so a compatible vacuum simulation may sample the corresponding CDT weights directly. It need not sample all primitive indices or multiply their raw norms into acceptance. NB, the gated native campaign, and the old toroidal force experiment retain their original definitions; they do not automatically measure this new branch. Its extended phase and \(G_R\) have not been measured.

## 15 Native proper-time sources and renewal that preserves coherence

The next bridge attaches the manuscript's retained rest generator to intrinsic causal duration. It also identifies a concrete renewal mistake and a compatible free-sector repair. [The clock and matter report](../Matter%20sector/chain_clock_2026-10-13/clock_matter_bridge_2026-10-16/CLOCK_MATTER_BRIDGE.md) gives the full calculations.

### 15.1 A native-energy prescribed source

Write the retained electron occupation projector as \(P_e\), avoiding confusion with the earlier events-per-simplex symbol. Appendix H.9 supplies \(T_e(s)=\exp(-\epsilon_e sP_e)\). With the selected H.9a identification \(s=\tau_\gamma/\tau_*\),

\[
U_e[\gamma]=\exp[-i\epsilon_e P_e\tau_\gamma/\tau_*],\qquad
\epsilon_e=4.18545879558\times10^{-23}.
\]

Proper durations add, so the transfer composes exactly along joined curves. This uses the native rest energy without introducing a separate gravitational charge. The proper-time attachment is a stated model choice; the rest spectrum alone does not derive it. An energy eigenstate contributes a phase, rather than a readable clock hand on every tick. Relative phases between paths can nevertheless depend on proper duration.

Two intrinsically transported normal geodesics were constructed on every one of the 1,920 new causal slabs. No history was rejected. Their durations vary across the ensemble, roughly from 6.54 to 6.99 ticks. The native logarithmic rest-transfer sewing error is \(1.72\times10^{-16}\), and actual joined-slab duration checks agree to rounding accuracy. The local Wick endpoint identity is checked for fixed curve segments; full reflection positivity of the marked path-selection rule is not proved by that identity.

The variation of duration is essential. One fixed-length timelike edge per slice has total length \(Ka\sqrt\alpha\). Its mass factor is independent of geometry and cancels from the connected two-source ratio. That observable has exactly zero connected rest-mass response at every volume. Larger simulations cannot repair that particular source definition.

For the varying prescribed curves, define

\[
Z(m_1,m_2)=\sum_Tp_0(T)e^{-m_1\ell_1(T)-m_2\ell_2(T)},\qquad
\partial_{m_1}\partial_{m_2}\log Z
=\operatorname{Cov}_{m_1,m_2}(\ell_1,\ell_2).
\]

The tested free-line covariance is \(-0.00171521593106\). At the native electron gap, the leading connected logarithm is \(-3.00472647\times10^{-48}\). Derivatives and logarithms retain this tiny signal; direct subtraction of nearly equal exponentials would not. A larger control mass verifies the derivative numerically, without replacing the physical rest gap.

These are nonstatic free lines in a tiny ensemble. Their negative covariance is not a repulsive Newton force or a value of \(G_R\). A static force requires the held-separation and duration limits described earlier. The prescribed-source route can proceed without a complete single-fermion theory.

### 15.2 Why equal fresh marginals do not guarantee interference

Consider a specified SWAP-reset dilation with every bath slot initially in \(\rho_*\). If two particle branches trigger \(n\) and \(m\) resets, the retained off-diagonal multiplier after tracing the bath is

\[
\gamma_{nm}=\operatorname{Tr}\rho_*^{|n-m|+1}.
\]

One extra reset gives only 0.0006036303 for the full native capacity distribution. The fresh marginal is correct on both branches, but the exported records distinguish their reset schedules. This is an explicit counterexample to inferring coherence from the marginal alone, not a theorem about every reset dilation.

The compatible free-sector choice follows H.11: renew local background cells independently of the retained particle's unmeasured position, and retain position and the mismatch fiber through renewal. Proper-time phase accumulation does not itself trigger extra erasures. On a fixed geometry,

\[
\mathcal E=\operatorname{id}_{X,Q}\otimes\mathcal E_{\rm background},
\qquad
\operatorname{Tr}_{\rm background}\mathcal E(\rho)
=\operatorname{Tr}_{\rm background}\rho.
\]

The retained-density error is \(5.73\times10^{-17}\). Spacelike-disjoint reset orderings agree to \(3.63\times10^{-17}\). This uses local event schedules; it requires no simultaneous global renewal. It does not establish gravitational refoliation independence or coherence between alternative geometries with different numbers of exported renewal events.

### 15.3 A sufficient positive-clock theorem

Given a supplied half-transfer \(A\) and positive middle-boundary duration operator \(N\), select

\[
K(m)=A^\dagger e^{-mN}A,\qquad
H(m)=-\frac1{\Delta t}\log K(m).
\]

On its fixed support, set \(C=-\partial_mK\). The derivative of the logarithm gives

\[
\partial_mH=\frac1{\Delta t}\int_0^\infty
(K+sI)^{-1}C(K+sI)^{-1}\,ds\succeq0.
\]

If \(N_{\min}I\preceq N\preceq N_{\max}I\), then

\[
\frac{N_{\min}}{\Delta t}I\preceq\partial_mH
\preceq\frac{N_{\max}}{\Delta t}I.
\]

Consequently \(iU_t^\dagger\partial_mU_t\) is a positive integrated clock and obeys the usual composition law. A seven-state supplied matrix fixture checks this theorem and its lift through the actual 169-by-seven connected geometric code. Positive entries in a source-weighted transfer alone do not imply it: a saved counterexample has a negative clock eigenvalue despite positive assigned entry lengths.

This sufficient theorem does not derive the actual duration operator. Replacing a distribution of durations by its mean loses higher cumulants. Making complete histories orthogonal intermediate labels can also remove coherent cross terms and change the transfer. The next construction therefore supplies a joint orbital generator explicitly rather than identifying those distinct constructions by assumption.

## 16 One finite geometry, particle, and clock model

The latest result supplies an actual joint operator and then realizes it in a finer microscopic cochain space. Geometry changes coherently while the particle moves. Its rest gap, proper-clock response, and evolution can all be checked in the same model. [The joint completion report](../Matter%20sector/chain_clock_2026-10-13/orbital_transfer_2026-10-16/JOINT_ORBITAL_COMPLETION.md) contains the scripts, six numerical result files, and three matrix archives.

### 16.1 Orbital motion within the retained sector

Use the manuscript's proposed Dirac-Kähler placement for position amplitudes on vertices, edges, faces, and tetrahedra. Keep the nine-state retained mismatch fiber \(Q\) intact; it is not renamed a Dirac spinor. For incidence coboundary \(d_p\) and positive cochain metric \(M_p\),

\[
d_p^*=M_p^{-1}d_p^\dagger M_{p+1},\qquad
D=d+d^*,\qquad
\Omega_g(m)=\sqrt{D_g^2+m^2I}.
\]

The square root is a selected positive-energy orbital completion. Rest modes satisfy \(D=0\) and have energy \(m\). Its mass-conjugate clock is

\[
\partial_m\Omega_g=m(D_g^2+m^2I)^{-1/2}.
\]

It equals one at rest and is positive at finite cutoff for \(m>0\). With supplied positive lapse, choose \(H_{\rm matter}=N^{1/2}\Omega_gN^{1/2}\). Adding any self-adjoint, mass-independent geometric coupling preserves positivity of the mass derivative. Real-time evolution is unitary, and

\[
\mathcal T(t)=iU_t^\dagger\partial_mU_t
=\int_0^tU_s^\dagger(\partial_mH)U_s\,ds
\]

is the integrated clock. Operator positivity of the Euclidean exponential does not imply entrywise nonnegative amplitudes or eliminate a sampling sign problem.

If the coarse spatial symbol is the desired metric symbol, \(E=\sqrt{h^{ij}p_ip_j+m^2}\), then \(d\tau/dt=Nm/E\), and the Legendre transform gives \(-m\int d\tau\). Thus motion, inertia, and the prescribed proper-time mass vertex agree without an additional gravitational coefficient. The condition on the spatial symbol is substantive and is tested below. As the momentum cutoff grows, \(m/E\) can approach zero; there is no uniform positive lower clock bound for all relativistic states.

The square root retains the components of both signs of the Dirac-Kähler spectrum. It does not resolve the particle/antiparticle assignment or the taste multiplicity into one physical fermion species. Those interpretations remain separate from proving self-adjointness.

### 16.2 The geometry transfer is enumerated

Take two physical spatial states. The first is the five-tetrahedron boundary of a four-simplex. The second replaces one tetrahedron by four regular tetrahedra. Here the second has a different physical metric; this is not an isometric refinement of the first. Their orbital cochain dimensions are 30 and 44.

The four boundary-pair families contain 1,920, 1,992, 1,992, and 2,064 causal slabs. Summing the same angular weights and using one common normalization gives

\[
A=\begin{pmatrix}
0.1169508311&0.3422031803\\
0.3422031803&1
\end{pmatrix}.
\]

Its smaller eigenvalue is negative. Use the positive two-step operator \(K_g=A^\dagger A\), whose eigenvalues are approximately \(1.85597649\times10^{-8}\) and 1.24788351. The logarithm is evaluated from the eigenvalues of \(A\) before squaring to protect numerical precision.

Set \(H_g=-\log K_g/\Delta t\) with the declared reference synchronization

\[
\Delta t=2a\sqrt{7+3/8}=13.94846613\,\tau_*
\]

in units \(c=1\). This is twice a particular boundary-normal duration. It does not assign that elapsed proper time to every moving path. The finite restriction is explicit; it is not a measured de Sitter phase or a proof of physical time independence from the chosen foliation.

### 16.3 Repairing an unintended mass shift

The raw stellar interpolation between the two physical cochain spaces has maximum singular value 1.48324. Using it directly as the off-diagonal geometry transport lowers the marked geometry-only ground energy by 0.131992 relative to the empty sector. That spurious shift is vastly larger than the native \(10^{-23}\) rest gap.

Normalize the transport separately on the harmonic rest modes and their orthogonal excited complements, using rectangular polar factors. With \(P_0,P_1\) the harmonic projectors, the resulting map obeys

\[
R^\dagger R=I,\qquad RP_0=P_1R.
\]

This is an explicit selected normalization. It is not assumed to intertwine the excited spatial operators on two different physical geometries. The marked geometric generator becomes

\[
\widehat H_g=\begin{pmatrix}
(H_g)_{00}I&(H_g)_{01}R^\dagger\\
(H_g)_{10}R&(H_g)_{11}I
\end{pmatrix}.
\]

Its lower bound is the empty-sector geometric ground energy \(E_{g,0}\). With unit reference lapse, \(\Omega_g(m)\ge mI\), and the transported harmonic modes attain the combined bound. Therefore

\[
\boxed{E_{\rm marked,0}(m)-E_{\rm vacuum,0}=m.}
\]

The native tiny gap is preserved algebraically after coupling geometry and matter. It is not inferred by subtracting floating-point eigenvalues at \(m=10^{-23}\). At the control mass 0.23, the gap error is \(4.45\times10^{-16}\). The vacuum transfer agrees with the enumerated \(K_g\) to \(4.45\times10^{-16}\), the clock derivative check to \(2.84\times10^{-10}\), and real-time unitarity to \(1.76\times10^{-15}\). A packet moves spatially and changes geometry coherently in the test. These establish joint finite behavior, not a physical transition probability prediction or a measured gravitational self-energy.

### 16.4 An exact microscopic metric for the whole operator

This result concerns coarse and fine descriptions of the same supplied coarse geometry. It must be distinguished from changing between the two physical geometries above. Let interpolation \(P\) and retraction \(R\) satisfy

\[
RP=I,\qquad d_fP=Pd_c,\qquad Rd_f=d_cR.
\]

Set \(Q_f=I-PR\), choose any positive auxiliary metric \(M_a\), and define

\[
\boxed{M_f=R^\dagger M_cR+Q_f^\dagger M_aQ_f.}
\]

Every fine vector has a unique decomposition \(Px+y\), with \(Ry=0\). Its norm is

\[
\|Px+y\|_f^2=x^\dagger M_cx+y^\dagger M_ay.
\]

The metric is positive, the coarse image is isometric, and the remaining cochains are orthogonal to it. Both subspaces are preserved by \(d_f\) and its metric adjoint. In orthonormal coordinates, the encoding \(J\) consequently obeys

\[
J^\dagger J=I,\qquad D_fJ=JD_c.
\]

Functional calculus carries over the entire orbital operator, clock, and evolution:

\[
\Omega_f(m)J=J\Omega_c(m),\qquad
(\partial_m\Omega_f)J=J(\partial_m\Omega_c),\qquad
e^{-it\Omega_f}J=Je^{-it\Omega_c}.
\]

This preserves the full supplied coarse dispersion, not just a selected mass or speed. It is an inverse construction of the microscopic inner product. It does not derive a good coarse operator from an unsuitable one: unwanted dispersion or extra species in the input are preserved too. The metric generally contains off-diagonal couplings; the refined cells are an orbital code, not an unchanged fine Regge metric.

Two explicit stellar refinements give dimensions \(30\to44\to58\). Direct and sequential interpolation agree exactly in the computation. Dirac intertwining agrees to \(5.99\times10^{-15}\), and the clock to \(3.85\times10^{-15}\). The two original harmonic modes remain, with no additional zero modes in the tested complement. This is refinement compatibility within the stated construction, not quantum refoliation independence.

Applying separate encodings inside each physical geometry and transporting their coupling gives a joint 74-to-102 dimensional lift, with the retained nine-state \(Q\) factor understood in both. The complete generator agrees to \(1.83\times10^{-13}\), the clock to \(7.79\times10^{-15}\), real-time evolution to \(3.11\times10^{-14}\), and two external test-source operators to \(1.83\times10^{-13}\). Complementary states do not mix with the prepared code. The source controls are not two calibrated held masses, and the complement is not claimed to lie above every excited code state.

### 16.5 The light-cone test still matters

The full Whitney metric, including off-diagonal integrals, reproduces a common low-momentum speed on flat embedded controls. Assigning every tetrahedron its intrinsic regular metric leaves a speed split. On the periodic BCC test the limits are

\[
v_0=\sqrt{5/6},\qquad v_T=\sqrt{4/5},\qquad v_3=\sqrt{3/4}.
\]

Thus neglecting off-diagonal entries was not the cause. A separate periodic inverse normalization uses the exterior-form metric of a chosen coarse geometry, fixed by its intrinsic volume before measuring the speeds. Both tested blocks then approach their common target cone. This is a constructive correction, without a fitted measured speed.

The irregular block still has a visible subleading transverse splitting, approximately linear in the tested wave number. Its relative spread is about \(9\times10^{-5}\) at the smallest tested diagonal momentum. The periodic correction also has not been assembled consistently over arbitrary changing CDT boundaries. It and the two-geometry spherical example therefore do not together prove a complete relativistic matter sector in one interacting model.

What is now concrete is the finite joint operator and its exact microscopic realization. What remains physical is whether one compatible many-boundary model has the required matter and gravitational long-distance behavior. The rest-gap identity does not determine \(G_R\); the geometry ensemble must supply the propagator and its normalization.


## 17 What the joined construction now establishes

The strongest result is a sequence of explicit compatible constructions. The original finite capacity state admits coherent binary cut modes. A selected absolute angular rule and paired-cell calibration give a bare curvature coefficient

\[
G_0/G_*=0.10551926870131369m_4^{8/3}=1.03002098319
\]

at the retained illustrative \(m_4=2.35\). Connected primitive geometric patches now realize the chosen Euclidean CDT weights at \(\alpha=7\). A finite joint geometry-orbital model preserves the native rest gap, evolves coherently, and has a positive mass-conjugate clock. Its complete operator has an explicit microscopic cochain realization.

The smooth selected metric action has the Einstein quadratic structure, two on-shell wave polarizations, and the tree-level Newton response derived earlier. That statement and the finite microscopic compatibility results are both useful. Their combination does not yet demonstrate that the interacting microscopic ensemble reaches that smooth gravitational regime.

| Result | Established scope |
|---|---|
| Native 1680-state encoding and local density matrix | Exact representation and a selected coherent global state. |
| Binary cut and curvature coefficient | Common tensor after selecting the absolute angular rule; near-unity bare value is conditional on the paired-cell calibration and provisional chain constant. |
| Einstein saddle and tree-level source response | Analytic structure and convergent finite checks of the selected metric action. |
| Connected primitive Euclidean geometry | Explicit full-rank interface maps; normalized contraction reproduces the selected CDT history weight. |
| Native proper-time source | Rest-energy insertion and joined-slab composition checked on all 1,920 histories. Free-line response is not a static force. |
| Renewal and path coherence | Background renewal preserves the retained sector on a fixed geometry; differing geometric event records remain an open interface. |
| Joint finite geometry, motion, and clock | One explicit two-geometry self-adjoint generator; vacuum CDT transfer and native rest gap preserved by selected normalization. |
| Microscopic refinement of the joint operator | Explicit positive metric and isometry preserve generator, clock, evolution, and transported test sources; numerical errors near \(10^{-13}\) or smaller. |
| Matter light cone and species | Raw regular-cell speed splitting persists. Periodic inverse correction fixes leading speeds in tested blocks; subleading splitting and general changing-boundary compatibility remain. |
| Physical time and refoliation | Reference synchronization and lapse are supplied; local and refinement checks are not full gravitational constraint closure. |
| Interacting gravitational phase and \(G_R\) | Not established for the new branch. Older runs retain their own ensemble definitions. |

The inverse construction is meaningful progress. It supplies interactions and a microscopic inner product that actually preserve the intended finite operator, rather than assuming that the raw microscopic contractions must have the right normalization. A uniqueness proof is not required for this existence result. The open empirical question is whether one fixed compatible construction realizes the desired long-distance physics.

The main conceptual danger has been changing the meaning of “finished.” A local normalization, a finite exact embedding, a tree-level Einstein response, and an interacting continuum theory are different claims. This revision records which one each calculation establishes, so that a new obstruction does not erase earlier results or get hidden by them.

## 18 Corrections that must travel with the results


| Earlier shortcut or interpretation | Retained correction |
|---|---|
| Local renewal implies Poisson spacetime events | Renewal concerns capacity marks; event placement needs its own invariant measure premise. |
| The last unknown is just events per simplex | That algebra is conditional on the physical clock, volume map, and Einstein interpretation of the measured mode. |
| Set the host edge equal to one tick | No such identity was derived; the current paired-cell calibration gives \(a\approx2.568L_*\). |
| Use \(\eta_*\) as an event probability because it matches | Withdrawn. Closure stiffness and event intensity are different quantities. |
| Fair binary occupation supplies vacuum entanglement | A separable mixture is a counterexample; coherent bonds were supplied explicitly. |
| Normalized replicas fix the geometric boost coefficient | The central-boost counterexample leaves it free; the absolute angular rule fixes it as a choice. |
| The pair parent on every edge is the graviton Hamiltonian | Its collective locking and soft-mode bound obstruct that interpretation. |
| The 0.016 percent current error establishes refoliation | It is a count-discretization error at fixed spatial regulator, not the full deformation-algebra error. |
| Every negative loop is the conformal direction | Shape-only stencils also retain frustrated loops. |
| Positive wave sampling plus a static source measures Newton gravity | Static density requires the constrained non-wave response. |
| A spatial \(\Omega^8\) density can simply be inserted into the transfer | Kernel normalization transforms with the density; inserting it twice changes the model. |
| The clock stops when volume turns around | The retained positive-lapse clock can continue through a volume turning point. |
| A zero lapse means the underlying finite dynamics is nonunitary | The inverse-lapse clock representation becomes singular; reference-time unitarity may remain. |
| Positive propagator covariance establishes attraction | Whole-volume fluctuations or preparation effects can dominate it. |
| A shortest path in one corridor certifies held separation | It supplies a candidate path; global lower bounds and alternate routes are needed. |
| Source-validity filtering is harmless | It changes the geometry ensemble; incomplete coverage suppresses the response. |
| The scheduled/native results already establish \(G_R\) | No such outputs were used in this archive or consolidation. |


| Later shortcut or interpretation | Retained correction |
|---|---|
| The new integer-channel model is what NB and the old force run already sample | It is a separate \(\alpha=7\) branch. Existing ensembles and their findings are unchanged. |
| Connected patches are already literal finer tetrahedral balls | The full-rank result is an abstract connected spin network; the tested literal balls have a rank deficit. |
| Correct fresh capacity marginals guarantee coherent particle paths | A branch-dependent reset schedule can leave distinguishing records. The fixed-background repair makes renewal independent of particle occupancy. |
| Every positive source-weighted matrix gives a positive clock | Positivity of the mass derivative requires operator structure; entrywise positivity alone fails in a saved counterexample. |
| Exact rest-gap preservation measures gravitational renormalization | It proves the selected finite transport normalization. It does not determine the long-distance gravitational propagator or \(G_R\). |
| Exact microscopic refinement proves the input has the right light cone | Refinement preserves the supplied operator, including any wrong dispersion or unwanted species. |
| The finite two-geometry clock is already full local physical time | Its synchronization and lapse are declared inputs; refoliation and general marked-boundary matching remain unproved. |

## 19 What remains and what can already be tested

The remaining work is now more specific than “find a microscopic model.” There is a finite joint operator and a constructive route into the microstructure. The next requirement is to make one compatible many-boundary construction exhibit the intended infrared matter and gravitational poles. The periodic cone correction must fit its changing geometry, with a consistent particle/antiparticle and species interpretation. Exported renewal records and the physical clock must match that same model. The geometry ensemble must also reach an extended regime with a controlled source response.

A prescribed-source force calculation can proceed before the complete fermion sector is solved. It needs geometry-dependent proper lengths, valid held trajectories, a separation window well above the regulator and below the box size, sufficiently long physical duration, and an equilibrated ensemble. The tiny old toroidal diagnostic remains informative within its limits, but it cannot be promoted into a measurement of the new branch simply because the bare normalization is shared.

For a fixed candidate, the force test is to measure the interaction at multiple separations and durations without retuning the bare coupling, mass, or clock to obtain agreement. Report \(G_R\) only if the measured regime supports that inference. Selecting and documenting a different microscopic construction is legitimate theory work; it defines a new candidate and a new test, not a retrospective change to a registered result.

At low curvature the desired effective functional is

\[
\Gamma[g,\psi]=\frac1{16\pi G_R}\int\sqrt{-g}(R-2\Lambda)
+\Gamma_m[g,\psi]+\Gamma_\partial+\sum_i c_i\mathcal O_i.
\]

The selected Einstein action and its flat graviton pole do not determine all higher-curvature coefficients, physical boundary data, or the renormalized coefficients of the interacting ensemble. An action also specifies a family of spacetime solutions; it cannot specify one universal spacetime function without initial and boundary conditions. [S06](SOURCES.md#s06), [S25](SOURCES.md#s25)

The current result is therefore an explicit finite microscopic realization with a selected Einstein target, a native-energy source bridge, and a joint particle-clock construction. Its unresolved physical tests are stated above. The original archive preserves the earlier derivations and failed routes; the linked evening reports supply the new matrices and checks. No manuscript revision, new geometry simulation, or new campaign analysis was performed to update this explanation.
