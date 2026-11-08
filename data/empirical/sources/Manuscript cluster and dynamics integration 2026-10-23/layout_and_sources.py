from pathlib import Path
import shutil,datetime,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
out=HERE/'iteration_sources'/datetime.datetime.now().strftime('%Y%m%d_%H%M%S');out.mkdir(parents=True)
p=ROOT/'01 Current Papers/Astra Full/Entropic Scalar EFT.tex';shutil.copy2(p,out/p.name)
s=p.read_text(encoding='utf-8');a=s.index('The same cells also carry a quantum spatial geometry.');b=s.index('\n\n',a)
s=s[:a]+r'''The cells also carry quantum spatial geometry. Coherent bonds preserve local probabilities and carry one bit of entanglement per cut. One angular rule fixes the cut entropy and curvature weight, linking the horizon area law and bare Einstein coefficient; a provisional event-volume calibration places that coefficient within three percent of the electron-anchored value. Connected patches reproduce the causal-dynamical-triangulation weight. At $\alpha=7$, the registered volume-stiffness ratio $G_{\rm vol}/G_0=1.064$ has logarithmic standard error $0.089$, with supporting stationary profiles at 16k and 64k. Start independence and matter response remain unresolved. Directional bond counts reconstruct a metric whose selected Einstein dynamics give Newton's law, two tensor polarizations, and Kasner expansion. A uniform-geometry construction has a positive physical inner product; a finite matter model preserves rest mass and clock during coherent propagation.''' +s[b:]
p.write_text(s,encoding='utf-8')
base=ROOT/'01 Current Papers/Empirical Results'
# Put the Bullet figure with its comparison text, without a nearly empty float page.
p=base/'Empirical_Results.tex';shutil.copy2(p,out/p.name)
s=p.read_text(encoding='utf-8').replace(r'\usepackage{graphicx,booktabs,tabularx,longtable,array}',r'\usepackage{graphicx,booktabs,tabularx,longtable,array,float}')
p.write_text(s,encoding='utf-8')
p=base/'05b_clusters.tex';shutil.copy2(p,out/p.name);s=p.read_text(encoding='utf-8')
s=s.replace(r'\begin{figure}[htbp]',r'\begin{figure}[H]').replace(r'\begin{table}[htbp]',r'\begin{table}[H]')
# Use the recovered targets once, and retain the scientific limits in compact form.
a=s.index('For central lensing targets,');b=s.index(r'\subsection{The Bullet Cluster',a)
s=s[:a]+r'''The central A1795 and A2029 lensing targets require respectively
48.2\% and 29.6\% of the minimal cohort's initial baryons outside the
aperture; for A1795 this is $7.87\times10^{13}\Msun$. Twelve finite
transport maps preserve positive marginals for the seven hydrostatic
and five lensing targets. This inventory construction leaves the
assembly time and work requirement undetermined. \source{CL3}

The gas must obey the same total potential,
\begin{equation}
a_g=-g-\frac{P_{\rm th}'+P_{\rm nt}'}{\rho_g}+\frac{f_{Cg}}{\rho_g}.
\end{equation}
Segregation, acceleration, and reciprocal contact are possible contributions.
Passive drag vanishes at zero drift, so stationary contact support requires
its own physical law. XRISM's low turbulent support in A1795 and A2029
constrains a purely turbulent explanation. \cite{sarkarnew,xrismnew}
The conditional pressure audit also depends on inner lensing extrapolation
and thermal reconstruction; a joint fit remains open.

A644's 58-knot forward profile contains 11 negative total-mass increments
and 15 negative stock increments. A monotone reconstruction requires
2.156 marginal error units of maximum displacement; absent joint
covariance, this is not an exclusion significance. Positive parametric
profiles require comparison with the underlying gas data. For ZW1215,
at 1320 kpc the correlated NFW-lensing, aperture-lensing, and hydrostatic
estimates are $4.32$, $7.0$, and $7.41\times10^{14}\Msun$. Both systems
retain reconstruction uncertainty rather than a new gravity coefficient.

''' +s[b:]
p.write_text(s,encoding='utf-8')
p=base/'05c_cross_sector.tex';shutil.copy2(p,out/p.name);s=p.read_text(encoding='utf-8')
for a,b in [(r'\source{U1, S03}',r'\source{U1, S03}\cite{sparcnew}'),(r'\source{U1, S04}',r'\source{U1, S04}\cite{kidsnew}'),(r'\source{U1, S05--S06}',r'\source{U1, S05--S06}\cite{actnew}'),(r'\source{U1, S09}',r'\source{U1, S09}\cite{egnew}'),(r'\source{U1, S11}',r'\source{U1, S11}\cite{constantsnew}'),(r'\source{U1, S12; D1}',r'\source{U1, S12; D1}\cite{gwtcnew}')]:s=s.replace(a,b)
p.write_text(s,encoding='utf-8')
p=base/'07_references.tex';shutil.copy2(p,out/p.name);s=p.read_text(encoding='utf-8')
s=s.replace('\\begin{thebibliography}{99}\n\\small','\\begin{thebibliography}{99}\n\\small\n\\setlength{\\itemsep}{3pt}\n\\setlength{\\parskip}{0pt}')
refs=r'''
\bibitem{sparcnew} SPARC collaboration, \href{https://astroweb.case.edu/SPARC/}{public rotation-curve and baryonic-mass data}. Selections and nuisance priors are recorded in U1, S03.
\bibitem{kidsnew} KiDS collaboration, \href{https://kids.strw.leidenuniv.nl/sciencedata.php}{public science data}; T. Mistele et al., \href{https://arxiv.org/abs/2310.15248}{arXiv:2310.15248}, updated acceleration table. Covariance conventions are recorded in U1, S04.
\bibitem{actnew} ACT collaboration, \href{https://github.com/ACTCollaboration/DR6-ACT-lite}{DR6-ACT-lite} and \href{https://lambda.gsfc.nasa.gov/product/act/act_dr6.02/index.html}{DR6 public products}; lensing analysis \href{https://arxiv.org/abs/2304.05202}{arXiv:2304.05202} and \href{https://arxiv.org/abs/2304.05203}{arXiv:2304.05203}.
\bibitem{egnew} ACT--BOSS lensing--velocity analysis, \href{https://arxiv.org/abs/2405.12795}{arXiv:2405.12795}. Band and redshift conventions are recorded in U1, S09.
\bibitem{constantsnew} NIST, \href{https://physics.nist.gov/cuu/Constants/}{CODATA reference values}; Particle Data Group, \href{https://pdglive.lbl.gov/DataBlock.action?node=S035M}{tau mass data}. The archived comparison values are recorded in U1, S11.
\bibitem{gwtcnew} LIGO--Virgo--KAGRA, \href{https://dcc.ligo.org/LIGO-P2600128/public}{public GWTC-4 gravity-test products}. The polarization evidence combination is recorded in U1, S12.
'''
s=s.replace(r'\end{thebibliography}',refs+'\n'+r'\end{thebibliography}');p.write_text(s,encoding='utf-8')
print('Abstract, cluster layout, and primary data references refined')
