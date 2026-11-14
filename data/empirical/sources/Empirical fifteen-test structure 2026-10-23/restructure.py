from pathlib import Path
import json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
P=ROOT/'01 Current Papers/Empirical Results'
def read(n):return (P/n).read_text(encoding='utf-8')
def write(n,s):(P/n).write_text(s,encoding='utf-8')

s=read('05c_cross_sector.tex')
def segment(a,b):return s[s.index(a):s.index(b)]
local=segment('For 130 selected','\\subsection{CMB spectra')
cmb=segment('The positive-allocation cosmology','The lensing--velocity statistic')
eg=segment('The lensing--velocity statistic','The best-fit vacuum density')
wide=segment('With the parent-carrier rule','The selected particle-coefficient route')
constants=segment('The selected particle-coefficient route','For a constant Einstein coefficient')
tensor=segment('For a constant Einstein coefficient','Three eight-Gyr halo')
halo=segment('Three eight-Gyr halo','\\subsection{Common-normalization')
disk=segment('At $a_0=1.2588','The moving-LMC satellite grid')
dwarfs=s[s.index('The moving-LMC satellite grid'):]

bench=r'''\section{Established tests from galaxies to gravitational waves}
\label{sec:benchmarks}

The local acceleration relation, lensing spectra, and tensor propagation
test whether the effective branches recover measured phenomena already
described by MOND or conventional gravitating matter and general relativity.
Their selections and covariance treatments remain separate. Overlapping
catalogues and spectra require a joint likelihood before their evidence
can be combined. \source{U1}

\subsection{Local RAR and baryonic Tully--Fisher}
\label{sec:localrar}
'''+local.replace('The isolated-lens audit',r'\subsection{Galaxy weak lensing}'+'\n'+r'\label{sec:galaxylensing}'+'\nThe isolated-lens audit')+r'''
\subsection{Primary CMB spectra and projected Weyl power}
\label{sec:cmb}
'''+cmb+r'''
The ACT lensing calculation tests projected Weyl power. A DESI full-shape
clustering likelihood with survey windows, bias, and redshift-space
distortions, and a nonlinear weak-lensing likelihood, remain open.
\source{U1, S06}

\subsection{Gravitational slip and the lensing--velocity statistic}
\label{sec:eg}
'''+eg+r'''
\subsection{Tensor polarization and propagation}
\label{sec:tensor}
'''+tensor
write('05c_cross_sector.tex',bench)

distinct=r'''\section{Common coefficients and additional discriminants}
\label{sec:discriminants}

\subsection{A common CMB-to-galaxy normalization}
\label{sec:crossnorm}
The bare commitment ratio and galactic scale obey
\begin{equation}
\frac{\rho_{C,i}}{\rho_{b,i}}=\frac1\epsilon,\qquad
a_0(z)=\epsilon cH(z),\qquad
a_0(z)\frac{\rho_{C,i}}{\rho_{b,i}}=cH(z).
\end{equation}
The fitted formation convention includes the mass-conversion factor
$f_m=5.333\epsilon$, and release leaves the homogeneous survival factor
$s(z)=e^{-\eta_*F(z)}$. On the undepleted background branch, the
observable stock ratio therefore satisfies
\begin{equation}
a_0(z)\frac{\bar\rho_C(z)}{\bar\rho_b(z)}=f_m s(z)cH(z).
\label{eq:crossnorm}
\end{equation}
The fitted $H_0=68.9389\,\kms\,\mathrm{Mpc}^{-1}$ gives
$a_0(0)=1.2588\times10^{-10}\,\mathrm{m\,s^{-2}}$, about 2.3\%
above the reference value, without a separate fit of $a_0$.
This is a conditional relation between sectors. Cosmological abundance
and $H_0$ are inferred together; galaxy mass calibration limits the
elementary empirical comparison to roughly twenty percent. The phase
loading and mass convention retain their physical matching assumptions.
\source{U1, S02; T4--T5}

\subsection{Newton's constant and charged-lepton masses}
\label{sec:constants}
'''+constants+r'''
\subsection{Halo tilt and a common Milky Way--LMC history}
\label{sec:halo}
'''+halo.replace('The earlier\nCrater II, Antlia 2, and tidal-dwarf calculations retain their stated\nselection and dynamical limits. \\source{U1, S13--S14; G3--G7}',r'''A common
Milky Way--LMC--stream fit remains open. The archived Galactic masses
inside 50 kpc exceed the cited constraint; Section~\ref{sec:jointtest}
quantifies that mismatch. \source{U1, S13; G3--G7}''')+r'''
\subsection{Old-disk vertical gravity}
\label{sec:olddisk}
'''+disk+r'''
\subsection{Wide binaries and Solar-System null tests}
\label{sec:binaries}
'''+wide
write('05d_distinctive.tex',distinct)

s=read('04_dwarfs.tex').replace(
 '\\section{Result 3: Crater II becomes cold through tidal loss of stock}',
 '\\section{Cold dwarf remnants and tidal inheritance}')
i=s.index('\\subsection{Antlia 2:');s=s[:i]+dwarfs+'\n'+s[i:]
write('04_dwarfs.tex',s)
for name,old,new in [
 ('02_acceleration.tex','Result 1: the acceleration scale changes with cosmic expansion','A cosmological acceleration scale: prediction and tension'),
 ('03_history.tex','Result 2: the LMC retains a massive gravitational profile','The LMC and inherited gravitating stock'),
 ('05_cosmology.tex','Result 4: dark energy from assembly and mixing','Dark energy, distances, and the primary CMB fit')]:
 s=read(name);assert old in s;s=s.replace(old,new,1);write(name,s)
s=read('05_cosmology.tex').replace('\\subsection{The matched linear-lensing likelihood}',
 '\\subsection{The matched linear-lensing likelihood}\n\\label{sec:distances}')
write('05_cosmology.tex',s)

intro=r'''\section{The empirical picture}

A common microscopic coefficient connects the proposed galactic
acceleration scale, the initial gravitating stock, and the fraction
converted into vacuum energy. The empirical question is whether those
connections survive observations of systems with different formation
and tidal histories while recovering the established gravitational and
cosmological benchmarks.

Two kinds of result carry different evidential weight. Distinctive tests
compare the common normalization, inherited stock, or response history
with specified alternatives. The LMC mass comparison, Crater II tidal
evolution, and NGC~628 vertical gravity give favorable results against
the tested QUMOND prescriptions or NFW populations. Their scope is set
by those comparisons. Conventional halos also retain assembly history,
and cored halos or other MOND implementations require their own tests.
High-redshift kinematics remains a tension; binary and halo predictions
still require broader observational likelihoods.

Established benchmarks test the local acceleration relation, weak
lensing, acoustic spectra, expansion distances, cluster gravity, and
tensor propagation. Near-equal CMB and distance fit quality demonstrates
that the selected cosmological branch can recover those observations.
The release history contains a fitted mixing parameter. Cluster
inventories and conservative encounters specify targets and mechanisms;
a shared-coupling population fit remains open.

\begingroup\small
\setlength{\tabcolsep}{4pt}
\renewcommand{\arraystretch}{1.10}
\begin{longtable}{@{}p{.06\textwidth}p{.24\textwidth}p{.56\textwidth}p{.06\textwidth}@{}}
\caption{All fifteen test families in the evidence register. Placement
identifies the role of a test; the status column states its present reach.
The register is exploratory, with the existing outcomes known.}\label{tab:fifteen}\\
\toprule ID & Test & Present result and limit & See\\\midrule
\endfirsthead
\toprule ID & Test & Present result and limit & See\\\midrule
\endhead
\multicolumn{4}{@{}l}{\textbf{I. Distinctive predictions and discriminating tests}}\\[3pt]
S01 & High-redshift kinematics & Reference line projection agrees; galaxy catalogue residuals retain a high-redshift tension. & \ref{sec:redshift}\\
S02 & CMB--galaxy normalization & Common-fit $a_0=1.2588\times10^{-10}\,\mathrm{m\,s^{-2}}$; conditional mass and survival factors. & \ref{sec:crossnorm}\\
S10 & Binaries and Solar System & Cassini null benchmark is compatible; a Gaia catalogue likelihood remains open. & \ref{sec:binaries}\\
S11 & $G$ and lepton masses & Close selected-formula values; finite routing tests leave discovery bias unquantified. & \ref{sec:constants}\\
S13 & Milky Way, LMC, streams, tilt & LMC mass agreement and repeated tilt realizations; Galactic mass and a joint stream fit remain unresolved. & \ref{sec:lmc}\\
S14 & Satellites and tidal dwarfs & Crater II favors stock within the tested grids; Antlia 2 and odds depend strongly on model error. & \ref{sec:crater}\\
S15 & Old-disk vertical gravity & NGC~628 gives $\chi^2=2.04$ for five dispersions; a broader tracer and force comparison is needed. & \ref{sec:olddisk}\\
\midrule
\multicolumn{4}{@{}l}{\textbf{II. Recovery of established phenomenology}}\\[3pt]
S03 & Local RAR and BTFR & Broad SPARC diagnostic and small BTFR scatter; the score is sensitive to velocity errors. & \ref{sec:localrar}\\
S04 & Galaxy weak lensing & Updated fifteen-bin diagonal score 10.06; reduction sensitivity and joint covariance remain. & \ref{sec:galaxylensing}\\
S05 & CMB acoustic peaks & Planck-based matched fit and ACT comparison recover similar quality to the reference cosmology. & \ref{sec:cmb}\\
S06 & Growth and Weyl power & ACT lensing score 16.21 over ten bins; DESI full-shape and nonlinear growth tests remain open. & \ref{sec:cmb}\\
S07 & Dark-energy history and distances & Matched BAO/SN fit with exponential allocation; independent mixing normalization remains open. & \ref{sec:distances}\\
S08 & Relaxed and colliding clusters & Positive stock targets and conserved encounters; outlier mechanisms and lens-map fits remain conditional. & \ref{sec:clusters}\\
S09 & Slip and $E_G$ & Transfer predictions are compatible with two published estimates; a joint window-convolved fit is needed. & \ref{sec:eg}\\
S12 & Waves and Lorentz tests & Luminal tensor branch is compatible with the polarization benchmark; operator-level Lorentz tests remain open. & \ref{sec:tensor}\\
\bottomrule
\end{longtable}
\endgroup
\source{U1; CL1--CL3; D1--D2}

The following calculations retain their individual likelihoods,
selection effects, and error models. A simulation realization, a fitted
relation, a conditional normalization, and an observation predicted
before measurement have different evidential roles. Lean checks the
stated mathematical implications; observed agreement is assessed
separately for each test.

\paragraph{Relation to the theory and CDT accounts.}
The effective astrophysical calculations use \emph{Entropic Scalar EFT}.
The companion CDT account distinguishes the electron-anchored scale
$G_*$, the selected bare coefficient $G_0\simeq1.03002G_*$, and an
interacting response $G_R$. The measured Newton constant remains the
effective input here. Matter response and the continuum phase of the
$\alpha=7$ CDT branch retain their own tests. \source{T1--T5}

'''
s=read('01_results_and_basis.tex');s=intro+s[s.index('\\section{The common microscopic coefficients}'):]
write('01_results_and_basis.tex',s)

s=read('Empirical_Results.tex')
s=s.replace('\\newcommand{\\source}[1]{\\textcolor{teal}{\\small [#1]}}',r'''\newcommand{\source}[1]{\textcolor{teal}{\small [#1]}}
\newcommand{\empiricalpart}[2]{%
  \clearpage\phantomsection
  \addcontentsline{toc}{part}{#1. #2}%
  {\Large\bfseries\color{ink}Part #1. #2\par}\vspace{6mm}}
''')
a=s.index('{\\large Galaxy accelerations across cosmic time');b=s.index('\\vspace{4mm}',a)
s=s[:a]+r'''{\large Distinctive predictions and discriminating tests\par}
\vspace{3mm}
{\large Recovery of established phenomenology\par}
\vspace{3mm}
{\normalsize Fifteen test families, with their evidence and open limits\par}
'''+s[b:]
s=s.replace('\\input{01_results_and_basis.tex}\n\\clearpage\n\\input{02_acceleration.tex}',
 '\\input{01_results_and_basis.tex}\n\\empiricalpart{I}{Distinctive predictions and discriminating tests}\n\\input{02_acceleration.tex}')
a=s.index('\\input{04_dwarfs.tex}');b=s.index('\\input{06_interpretation_and_audit.tex}',a)
s=s[:a]+r'''\input{04_dwarfs.tex}
\clearpage
\input{05d_distinctive.tex}
\empiricalpart{II}{Recovery of established phenomenology}
\input{05c_cross_sector.tex}
\clearpage
\input{05_cosmology.tex}
\clearpage
\input{05b_clusters.tex}
\clearpage
'''+s[b:]
write('Empirical_Results.tex',s)

s=read('06_interpretation_and_audit.tex')
a=s.index('The strongest present numerical agreements');b=s.index('\\subsection{The derivation',a)
s=s[:a]+r'''The LMC enclosed masses and NGC~628 vertical dispersions support
the retained-stock prescription against the tested external-field and
algebraic QUMOND comparisons. Crater II gives a favorable comparison
with a specified NFW population, with strong dependence on the error
budget. The reference acceleration-line projection agrees, while the
high-redshift catalogue test retains a residual trend. The matched
cosmology recovers CMB and distance data with a tied abundance; ACT
lensing and $E_G$ add compatible checks. These results establish the
scope of the particular comparisons summarized in Table~\ref{tab:fifteen}.
Antlia 2, cluster outliers, Galactic mass, and independent release
normalization remain active constraints.

'''+s[b:]
s=s.replace('\\subsection{A joint test of the same construction}',
 '\\subsection{A joint test of the same construction}\n\\label{sec:jointtest}')
s=s.replace('The\nreference-curve agreement and the cosmological best fit are presently\nseparate calculations.',
 'The catalogue diagnostics and old-disk check already use the common-fit\nnormalization; the full galaxy-assembly and cosmological likelihood remains\na joint inference problem.')
write('06_interpretation_and_audit.tex',s)

labels={'S01':'sec:redshift','S02':'sec:crossnorm','S03':'sec:localrar','S04':'sec:galaxylensing',
 'S05':'sec:cmb','S06':'sec:cmb','S07':'sec:distances','S08':'sec:clusters','S09':'sec:eg',
 'S10':'sec:binaries','S11':'sec:constants','S12':'sec:tensor','S13':'sec:lmc','S14':'sec:crater','S15':'sec:olddisk'}
register=json.loads((ROOT/'02 Research/Unified empirical program 2026-10-23/execution_register.json').read_text())
text='\n'.join(p.read_text(encoding='utf-8') for p in P.glob('*.tex'))
assert set(labels)=={r['id'] for r in register['sectors']}
for label in labels.values():assert '\\label{'+label+'}' in text,label
(HERE/'coverage.json').write_text(json.dumps([{'id':r['id'],'title':r['title'],'location_label':labels[r['id']],
 'part':'I' if r['id'] in ['S01','S02','S10','S11','S13','S14','S15'] else 'II',
 'status_snapshot':r['status']} for r in register['sectors']],indent=2),encoding='utf-8')
print('Reorganized all 15 test families; preserved numerical results and limitations.')
