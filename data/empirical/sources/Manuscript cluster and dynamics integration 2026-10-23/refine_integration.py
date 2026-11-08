from pathlib import Path
import json,shutil,re,datetime
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
stamp=datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
backup=HERE/'iteration_sources'/stamp;backup.mkdir(parents=True)
main=ROOT/'01 Current Papers/Astra Full/Entropic Scalar EFT.tex'
shutil.copy2(main,backup/main.name);s=main.read_text(encoding='utf-8')
a=s.index('Diffuse source projection $\\epsilon=');b=s.index('Bounded capacity $q$',a)
s=s[:a]+r'''Cluster cohort normalization & cluster sector & Fixed budget; transport conditional & $k_C=e^{-\eta_*}/\epsilon=5.1760752$ fixes the closed cohort. Aperture baryons and stock can have different retained fractions; their histories require forward evolution. & \S18, App.~O.3 \\
\hline
Reciprocal finite-work contact & effective dynamics & Conservation identities and controlled encounters & Central pair transitions conserve linear and angular momentum; work and heat balance kinetic changes. The floor gates inaccessible transitions. Physical target, rate, and range remain selected inputs. & \S18, App.~O.3 \\
\hline
Observed radial clusters & empirical targets & Positive nominal NFW inventories; coextensive outliers & Twelve X-COP profiles, seven stellar profiles, and five independent lensing masses. A1795 and A2029 require relative segregation under their central lensing targets; A644 and ZW1215 require reconstruction/estimator uncertainty. & \S18 \\
\hline
Bullet lensing and gas separation & cluster dynamics & Effective mechanism demonstrated; resolved fit open & Weak-contact encounters separate gas from stock near galaxies. The released Bullet map supplies aperture masses and a 3.92 kpc halo--galaxy target, below the illustrative simulation resolution. & \S18 \\
\hline
Depleted capacity & covariant effective action & Positive resting state on a selected regular branch & A constant floor gives $\rho\to K$, $p\to-K$, and vanishing source-clock current. The tested background stays on the unchanged dust branch. Constitutive selection, null interfaces, and nonlinear evolution remain open. & App.~O.3 \\
\hline
''' +s[b:]
s=s.replace('The positive-allocation likelihood and an independently measured retention gate remain to be tested. The cluster lift needs its coherence profile and resolved lensing-map test,','The positive-allocation likelihood is implemented; an independently measured retention gate remains to be tested. The conservative cluster contact needs physical selection and a resolved lensing-map fit,')
s=s.replace('Clusters and mergers require physical channel selection','Clusters and mergers require physical contact selection')
s=s.replace('Supported across heterogeneous tests; no combined significance assigned','Mixed empirical results; no combined significance assigned')
s=s.replace('The cluster capacity bound, committed abundance, redshift direction of $a_0$, and low-acceleration rotation-curve regime remain post-fixation tests of the original ensemble;','The cluster budget, committed abundance, redshift dependence of $a_0$, and low-acceleration rotation-curve regime are empirical tests of the original ensemble;')
s=s.replace(r'\paragraph{Growth-limited kernels.} For development dynamics',r'\paragraph{Growth-limited kernels.} An auxiliary phase-weight model supplies a diagnostic of a proposed free-fall response clock; its weights do not replace the transported mass inventory of Section~18. For development dynamics')
extra=r'''
At the common cosmological acceleration normalization, the reduced
old-disk solver gives NGC~628 a completion $\chi^2=2.04$ for five
dispersions and a $-0.21\sigma$ radial--vertical mass offset; its
approximate algebraic QUMOND comparison gives $8.95$ and $-2.91\sigma$.
The gas profile, inclination, scale height, and population selection
remain physical uncertainties. A round conventional halo can also give
similar vertical gravity. In the saved satellite grid, increasing the
model-error allowance from ten to thirty percent changes the Crater~II
stock/NFW evidence from $2.6\times10^5$--$2.0\times10^8$ to 94--155,
and Antlia~2 from 0.007--0.019 to 0.69--0.74. The prior and error model
therefore control much of the quoted evidence. These archived trajectories
have not been rerun with the conservative contact.

'''
s=s.replace(r'\subsection{27.1 Static weak-field falsifiers}',extra+r'\subsection{27.1 Static weak-field falsifiers}')
main.write_text(s,encoding='utf-8')
emp=ROOT/'01 Current Papers/Empirical Results'
p=emp/'05c_cross_sector.tex';shutil.copy2(p,backup/p.name)
s=p.read_text(encoding='utf-8')+r'''
\subsection{Common-normalization disk and dwarf checks}
At $a_0=1.2588\times10^{-10}\,\mathrm{m\,s^{-2}}$, the reduced
old-disk solver gives NGC~628 $\chi^2=2.04$ for five dispersions and
a $-0.21\sigma$ radial--vertical mass offset. The approximate algebraic
QUMOND comparison gives $\chi^2=8.95$ and $-2.91\sigma$. The small
normalization change preserves the earlier pattern. Gas-profile,
inclination, and scale-height uncertainties remain, and a round
conventional halo can give similar vertical gravity.
\source{U1, S15}

The moving-LMC satellite grid was reweighted with ten, twenty, and
thirty percent model uncertainty. At thirty percent the Crater II
stock/NFW evidence falls to 94--155 from $2.6\times10^5$--$2.0\times10^8$
at ten percent; Antlia 2 rises from 0.007--0.019 to 0.69--0.74.
The grid does not implement the new conservative joint-stock contact
or span broad cored-halo alternatives. Its evidence remains conditional
on the specified histories, priors, and error budget. \source{U1, S14}
'''
p.write_text(s,encoding='utf-8')
# Refresh only the plot of saved fit values; no fit or simulation is run.
figpath=emp/'figures/cosmology.pdf';shutil.copy2(figpath,backup/'cosmology.pdf')
d=json.loads((ROOT/'02 Research/Unified empirical program 2026-10-23/results/cosmology_final.json').read_text())['verification']
fig,axes=plt.subplots(1,2,figsize=(10,3.7),layout='constrained')
ax=axes[0];delta=d['geodesic']['total']-d['lcdm']['total']
ax.bar(['Exponential release (5)',r'$\Lambda$CDM (6)'],[delta,0],color=['#127c80','#526978'])
ax.axhline(0,color='black',lw=.7);ax.set_ylabel(r'$\Delta\chi^2$ relative to matched $\Lambda$CDM');ax.set_ylim(-.7,.18)
ax.text(0,delta-.035,f'{delta:.3f}',ha='center',va='top');ax.text(1,.02,'0.000',ha='center')
ax.set_title('Direct perturbations; linear lensing');ax.tick_params(axis='x',labelsize=9)
ax=axes[1]
for i,(lo,hi) in enumerate([(75.4,75.9),(93.1,96.7),(108,109.9)]):
 ax.plot([lo,hi],[i,i],lw=5,color='#127c80');ax.plot((lo+hi)/2,i,'o',color='#127c80')
ax.axvline(94.2,color='#b65d34',linestyle='--',label='Archived PPF target 94.2');ax.set_yticks([0,1,2],['17 km/s','14 km/s','12 km/s']);ax.invert_yaxis()
ax.set_xlabel(r'Archived linear-depletion $I_{\rm rel}$');ax.set_ylabel('Retention gate');ax.set_title('Hydrodynamic kernel comparison');ax.legend(fontsize=8)
fig.savefig(figpath);plt.close(fig)
print('Claim table reconciled; disk/dwarf updates and saved-fit figure added')
