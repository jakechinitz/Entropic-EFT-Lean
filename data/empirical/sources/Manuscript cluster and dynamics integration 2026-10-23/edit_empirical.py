from pathlib import Path
import re,shutil,json,difflib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BASE=ROOT/'01 Current Papers/Empirical Results'
diffs=[]
def edit(name,fn):
 p=BASE/name;s=p.read_text(encoding='utf-8');t=fn(s)
 p.write_text(t,encoding='utf-8',newline='\n')
 diffs.extend(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='preserved/'+name,tofile='current/'+name))
def rep(s,a,b,n=1):
 assert s.count(a)==n,(a[:100],s.count(a),n)
 return s.replace(a,b)
def block(s,a,b,t):
 i=s.index(a);j=s.index(b,i);return s[:i]+t+'\n\n'+s[j:]
def cover(s):
 s=rep(s,'Four tests of a capacity-based spacetime model','Galaxy, cluster, and cosmological tests')
 s=rep(s,'{\\large Dark energy from the loss of source identity\\par}','{\\large Dark energy from the loss of source identity\\par}\n{\\large Conservative cluster dynamics and lensing\\par}')
 return rep(s,r'\input{06_interpretation_and_audit.tex}',r'\input{05b_clusters.tex}'+'\n\\clearpage\n'+r'\input{05c_cross_sector.tex}'+'\n\\clearpage\n'+r'\input{06_interpretation_and_audit.tex}')
edit('Empirical_Results.tex',cover)
def intro(s):
 s=rep(s,'Four groups of results test different parts of this account.','Galaxy, cosmological, and cluster results test different parts of this account.')
 s=rep(s,'Cosmological release & The geodesic-clock, linear-depletion fit gives\n$\\chi^2=2227.910$, versus $2228.429$ for','Cosmological release & The geodesic-clock, exponential-allocation fit gives\n$\\chi^2=2227.801$, versus $2228.316$ for')
 s=rep(s,'is fitted; the positive-allocation law needs a separate likelihood.','is fitted; nonlinear spatial evolution and the independent release\nnormalization remain open.')
 s=rep(s,r'\caption{The four principal empirical comparisons.',r'\caption{The principal galaxy and cosmological comparisons.')
 s=rep(s,'and a lensing correction,','and matched linear lensing,')
 return rep(s,r'\paragraph{Relation to the theory and CDT accounts.}',r'''Cluster encounters now use an explicit energy and momentum ledger,
with a contact that switches off at its work floor. Twelve X-COP profiles,
five independent lensing masses, and the public Bullet map provide
quantitative targets. The coextensive prescription is close to several
targets; A1795 and A2029 require relative baryon--stock segregation under
their central lensing masses. A completed shared-coupling fit remains open.
\source{CL1--CL3}

\paragraph{Relation to the theory and CDT accounts.}''')
edit('01_results_and_basis.tex',intro)
def acceleration(s):
 s+=r'''
\subsection{Catalogue tests and the direction of a relaxation correction}
The common cosmology was propagated to 73 KMOS3D, 21 KGES, and 169 KROSS
objects at three radii. At the KMOS3D outer radius, the log-acceleration
residual slope is $-0.245$ dex per unit redshift with constant $a_0$ and
$-0.313$ with the common $H(z)$ law. The latter has median log-velocity
residual $-0.087$ dex. The reference $z=2.3$ example gives acceleration
boosts about 2.02 versus 1.39 for the compared evolving and fixed scales.
These are catalogue central-value diagnostics with specified baryon force
models; they do not constitute raw-cube likelihoods. The 112-point
reference projection remains distinct from a regression on the actual
79-object MUSE selection. The common cosmology has not removed the
high-redshift residual trend. \source{U1, S01}

Passive relaxation cannot automatically supply a reduction. If
$\dot n=\Gamma(q-n)$ with $\Gamma>0$, $\dot q\le0$, and initially
$n\ge q$, then $n$ remains above the target. At fixed baryons a lag behind
declining $H$ therefore has the wrong sign to suppress an initially
equilibrated response. Underoccupied assembly states require their own
history. Relabeling an unchanged stock leaves its total stress unchanged;
the tested adiabatic cosmological mass loss gives an inferred scale ratio
0.9183 from $z=2.3$, compared with $H_0/H(2.3)=0.2972$.
These constraints identify the contact and preparation history as physical
requirements. \source{D1}

For the selected two-pole quantum response, the noise enhancement
$\mathcal F$ and mean delay $\bar\tau$ obey
$\mathcal F H\bar\tau\ge4$. The illustrative three-percent tracking
condition at occupation argument $x=1$ gives $\mathcal F\gtrsim158$,
requiring about $6.47\times10^4$ independent cells for three-percent
force rms. Actual windows, correlations, and gravitational coupling
remain unspecified, so this is a contact-model constraint.
\source{D1; T1, N.8}
'''
 return s
edit('02_acceleration.tex',acceleration)
def cosmo(s):
 s=rep(s,'$\\chi^2=2227.910$, against $2228.429$','$\\chi^2=2227.801$, against $2228.316$')
 s=rep(s,'and uses the linear-depletion background defined below.','and uses the exponential positive-allocation background defined below.')
 s=rep(s,'positive background law whose likelihood remains to be calculated.','positive background law used by this matched likelihood.')
 s=rep(s,'a distinct\npositive background','a\npositive background')
 # These endpoint replacements apply only to the matched direct fit.
 for a,b in [('0.02237988','0.02237932'),('0.28161367','0.27424478'),('0.68943454','0.68938856'),('3.04623641','3.04585067'),('0.96662615','0.96662931'),('0.05680213','0.05661582'),('589.185','589.078'),('1627.018','1627.016'),('2227.910','2227.801'),('590.329','590.215'),('2228.429','2228.316'),('68.9435','68.9389'),('-0.519','-0.515'),('-2.519','-2.515')]:
  s=s.replace(a,b)
 s=s.replace(r'\source{C4}',r'\source{C4, C5}')
 s=block(s,'The archived linear-depletion history at $f=0.282706$ gives','Early accumulation is compatible',r'''The fitted exponential-allocation history gives
\begin{align}
F_{\rm rel}(0)&=0.6635663,& z_{1/2}&=7.9278,\\
\frac{\rho_\Lambda(2)}{\rho_\Lambda(0)}&=0.9682403,&
e^{-\eta_*F_{\rm rel}(0)}&=0.9803765.
\end{align}
Here $z_{1/2}$ is the epoch at which the vacuum density first reaches
half its present value. About 65.8\% is present by $z=6$. The remaining
stock has lost 1.96235\% of its initial comoving mass, and the drain
between $z=1$ and today is only $0.49347\%$ of that initial stock.
The vacuum integral weights release by $a^{-3}$, so early release
contributes disproportionately to the accumulated density. These values
condition on the fitted kernel and reference assembly table. The
archived figure below retains its closely neighboring linear-depletion
history; it does not define the current likelihood. \source{C5}''')
 s=rep(s,'The positive-allocation model and\nany completion at total-stock exhaustion must be tested with their own\nbackground and perturbation equations.','The selected depletion completion below inherits the cold linear fit;\nits nonlinear spatial predictions require a separate test.')
 floor=r'''
\subsection{A self-limiting local completion and its coupling}
The unit-clock action is exact above a selected depletion threshold.
For $X=-\nabla_\mu\phi\nabla^\mu\phi/2$, a covariant continuation is
\begin{equation}
P=\lambda X-e-V,\quad L=3(K-V)>0,\quad
e=\frac\lambda2+\frac{2[L-\lambda]_+^3}{3L^2},\quad \lambda\ge L/2.
\end{equation}
The constant $K$ is a minimum total energy. For $\lambda>L$ the
Lagrangian is exactly $\lambda(X-1/2)-V$. On the intermediate branch
$r=\lambda/L\in(1/2,1)$, define $v=\sqrt{2X}$ and $j=\lambda v$.
Then $X=1/2-2(1-r)^2$ and
\begin{equation}
\dot j=-\left[\theta+\frac{V_\phi A(r)j}{\lambda^2}\right]j,
\qquad A(r)=\frac{1+2r-2r^2}{3-2r}\in[3/4,1].
\end{equation}
For regular flow with $K-V$ bounded away from zero, the current stays
nonnegative and the source field slows toward $j=0$,
$\rho=K$, $p=-K$. The regular sound speed lies between zero and one.
The constant minimum removes the scalar force at rest. This slows the
source field relative to proper time; no universal atomic-clock effect
has been established. The cubic and floor are constitutive choices.
\source{D1}

For the fitted history, the choice
$K=V(1)+B[e^{-\eta_*F(1)}-e^{-\eta_*}]$ bounds all remaining future
release under the stated monotonicity assumptions. The saved value is
$K=0.3369964$ in units $3H_{100}^2/(8\pi G)$, with
$\max_{a\le1}L/\bar C=0.0299937$. The background and a neighborhood of
its linear perturbations stay on the original branch. Hence the
completion inherits the fitted cold adiabatic linear cosmology. Deep
voids enter a pressure regime with a changed minimum energy and require
new expansion, profile, and lensing predictions. Nonzero-null-gradient
interfaces and nonlinear caustics remain unresolved.

A finite-work contact extends this mechanism to redistribution. For
a transition $E\to E'$ toward target $h$, let
$Q=\Theta\ln(h'/h)$, $W=E'-E+Q$, $U'=U-W$, and $E_B'=E_B+Q$.
Their total energy is conserved. A symmetric gate $v(U)v(U-W)$ allows
only admissible endpoints and vanishes at the floor. Central pair
impulses give reciprocal momentum exchange. The target and physical
rate require selection beyond detailed balance. \source{D2}

A warm fluid stress stores heat as $e_T=z n^\gamma\ge0$ with
$1<\gamma\le2$ and
$\rho=R_0(n,\phi)+e_T$, $p=p_0+(\gamma-1)e_T$.
Its sound speed is an enthalpy-weighted average of the cold speed squared
and $\gamma-1$, preserving the causal local bound and energy floor.
The gate $g=n\mu/(\lambda_0+\gamma e_T)\in[0,1]$ retains a regular
signed power $gB_c$ and reduces to the cold $v_0^2$ gate.
In the selected $\gamma=4/3$ compression test, five resolutions up to
2048 cells conserve mean total energy to $4.9\times10^{-15}$ and keep
positive current. Generated heat falls from 0.0641 to 0.0140 under
refinement, so physical dissipation has not converged. A separate
particle-feedback test has fractional energy error $1.02\times10^{-5}$
and stops short of the target when available work is insufficient.
These tests establish a conservative effective implementation; the
coupled spatial and multistream evolution remains to be validated.
\source{D2}
'''
 return s+floor
edit('05_cosmology.tex',cosmo)
for src,dst in [('empirical_clusters.tex','05b_clusters.tex'),('empirical_cross_sector.tex','05c_cross_sector.tex')]:
 s=(HERE/src).read_text();s=s.replace('only seven lies','only the integer $7$ lies').replace(r'\source{U1, S08}',r'\source{U1, S09}').replace(r'\source{U1, S09}',r'\source{U1, S09}')
 if src=='empirical_cross_sector.tex':
  s=s.replace(r'performed. \source{U1, S09}',r'performed. \source{U1, S10}').replace(r'\source{U1, S10--S11}',r'\source{U1, S11}')
 assert not (BASE/dst).exists()
 (BASE/dst).write_text(s,encoding='utf-8')
for src,dst in [('independent_lensing.png','cluster_lensing.png'),('bullet_observed_maps.png','cluster_bullet.png')]:
 shutil.copy2(ROOT/'02 Research/Observed cluster tests 2026-10-23/figures'/src,BASE/'figures'/dst)
def interpretation(s):
 s=s.replace('What follows from the four results','Joint interpretation').replace('four unrelated curve fits','unrelated curve fits').replace('68.9435','68.9389')
 s=rep(s,'The N-body campaigns, hydrodynamic run, cosmological optimizations, and\nLean build were not rerun for this synthesis.',r'''The dated research records include the exponential-allocation cosmological
optimization, finite-work and fluid tests, merger controls, observed cluster
reductions, and outlier audits. They were not rerun to typeset this paper.
Six extension modules contribute 119 explicit theorem declarations,
independently checked with the available Lean/mathlib 4.19 runtime and
added to the pinned library's import graph. Their build and axiom records
are separate from the upstream 4.35 audit. \source{T5}''')
 s=rep(s,'the current verification\nrecord uses the unrounded acceleration coefficient and imports the\nhigher-accuracy matched cosmology endpoints.','the current verification\nrecord uses the unrounded acceleration coefficient and the saved\nhigher-accuracy exponential-allocation cosmology endpoints.') if 'the current verification\nrecord uses' in s else s
 s=rep(s,'with the positive-allocation background, its interacting perturbations,\nand a matched full cosmological likelihood.','with the existing positive-allocation perturbation implementation and\na matched full cosmological likelihood.')
 key=r'''
T5 & \path{02 Research/Manuscript cluster and dynamics integration 2026-10-23}.
Preserved source hashes, integration diffs, six-module manifest, compilation
checks and PDF validation. The extension sources are also under
\path{Entropic/Extensions20261023} in the Lean library. \\
U1 & \path{02 Research/Unified empirical program 2026-10-23/execution_register.json}.
Fifteen-sector evidence register; S01--S15 identify the selected datasets,
saved results, source URLs, and remaining tests. \\
C5 & \path{02 Research/Unified empirical program 2026-10-23/results/cosmology_final.json}.
Exponential-allocation fit, matched reference, and saved observables. \\
D1 & \path{02 Research/Connected theory closure 2026-10-23}.
Depletion action, unchanged linear domain, lag and noise bounds, and
conditional tensor calculation; 42 Lean declarations. \\
D2 & \path{02 Research/Effective dynamics and coupling 2026-10-23}.
Finite-work contact, warm fluid stress, compression and feedback checks;
36 Lean declarations. \\
CL1 & \path{02 Research/Conservative cluster merger 2026-10-23}.
Seventeen encounter/control runs, conservation and refinement records;
8 Lean declarations. \\
CL2 & \path{02 Research/Observed cluster tests 2026-10-23}.
X-COP and MENeaCS profiles, Bullet v1 targets, source hashes, and
15 numerical/data-handling checks. \\
CL3 & \path{02 Research/Cluster outlier closure 2026-10-23}.
Conditional pressure and transport audit, A644 positivity test, twelve
finite transport maps, 14 saved checks, and 22 Lean declarations. \\
'''
 # Insert into the source table, not an earlier summary table.
 pos=s.index(r'\subsection{Local source key}');k=s.index(r'\bottomrule',pos)
 s=s[:k]+key+s[k:]
 s=rep(s,'The supplementary \\path{refresh_verified_results.py} updates the\nunrounded redshift projection and imports the saved matched-fit results;\nit preserves prior outputs before writing.',r'''The supplementary \path{refresh_verified_results.py} reproduces the
earlier matched-fit snapshot and preserves prior outputs. The current
exponential-allocation endpoints and cross-sector calculations are
identified by C5 and U1; the integration record preserves their hashes.
The earlier refresher is not the updater for this later snapshot.''')
 return s
edit('06_interpretation_and_audit.tex',interpretation)
def references(s):
 refs=r'''
\bibitem{xcopnew} S. Ettori et al., ``Hydrostatic mass profiles in X-COP galaxy clusters,'' A\&A 621, A39 (2019).
\href{https://arxiv.org/abs/1805.00035}{arXiv:1805.00035};
\href{https://dominiqueeckert.wixsite.com/xcop/data}{public X-COP data}.
\bibitem{herbonnetnew} R. Herbonnet et al., ``CCCP and MENeaCS: (updated) weak-lensing masses for 100 galaxy clusters,'' MNRAS 497, 4684 (2020), Table A2.
\href{https://arxiv.org/abs/1912.04414}{arXiv:1912.04414}.
\bibitem{bulletnew} G. Rihtar\v{s}i\v{c} et al., ``Mapping dark matter in the Bullet Cluster using JWST imaging and spectroscopy'' (2026).
\href{https://arxiv.org/html/2601.22245v2}{arXiv:2601.22245v2};
\href{https://niriss.github.io/lensing.html}{CANUCS Bullet v1 maps}.
\bibitem{sarkarnew} A. Sarkar et al., ``XRISM Observations of Abell 1795: Evidence for Low Turbulence and Resonant Scattering'' (2026).
\href{https://arxiv.org/abs/2606.08097}{arXiv:2606.08097}.
\bibitem{xrismnew} XRISM Collaboration, ``Constraining gas motion and non-thermal pressure beyond the core of the Abell 2029 galaxy cluster with XRISM'' (2025).
\href{https://arxiv.org/abs/2505.06533}{arXiv:2505.06533}.
'''
 return rep(s,r'\end{thebibliography}',refs+'\n'+r'\end{thebibliography}')
edit('07_references.tex',references)
(HERE/'empirical.diff').write_text(''.join(diffs),encoding='utf-8')
print('Empirical sources updated; two sections and two figures added')
