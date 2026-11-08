"""Update arithmetic and figures from saved inputs; launches no simulations or fits."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, shutil, argparse
import numpy as np
from scipy.integrate import cumulative_trapezoid
from scipy.interpolate import PchipInterpolator
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
default_root = next((p for p in HERE.parents if (p/'.organization/file_locations.csv').is_file()),None)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--workspace',type=Path,default=default_root)
parser.add_argument('--legacy-linear',action='store_true',help='Reproduce the preserved linear-depletion comparison instead of the current exponential fit')
args=parser.parse_args()
if args.workspace is None: parser.error('Provide --workspace with the original source workspace.')
ROOT = args.workspace.resolve()
FIT = ROOT/'02 Research/High leverage closure 2026-10-21'
LEAN = ROOT/'02 Research/Unified closure 2026-10-21/formalization'
paths = [HERE/'numerical_review.json', FIT/'fit_comparison.json',
         FIT/'fit_physical_geodesic/result.json', FIT/'fit_physical_lcdm/result.json',
         FIT/'cosmology_checks.json', FIT/'growth_independent_check.json',
         LEAN/'verification/axiom_audit_final_2026-10-23.log',
         LEAN/'verification/citecheck_final_2026-10-23.log', LEAN/'ledger/LEDGER.md',
         ROOT/'02 Research/Release zoom/Frel_table.npy', ROOT/'02 Research/Release zoom/zoom_fits.jsonl']
for p in paths:
    if not p.is_file(): raise FileNotFoundError(p)
archive = json.loads(paths[0].read_text())
comp, geo, lcdm, checks, growth = [json.loads(p.read_text()) for p in paths[1:6]]
a0 = archive['micro']['a0_SI'] / 1e-10
z = np.arange(33, 145, dtype=float)/100
y = a0*np.sqrt(.315*(1+z)**3+.685)
slope, intercept = np.polyfit(z,y,1)
assert abs(intercept-1.0027841274263571)<1e-12
assert abs(slope-1.2256453196424542)<1e-12
assert abs(comp['geodesic']['total']-geo['parts_higher_accuracy']['total'])<1e-10
assert abs(comp['lcdm']['total']-lcdm['parts_higher_accuracy']['total'])<1e-10
assert abs(comp['delta_chi2']-(comp['geodesic']['total']-comp['lcdm']['total']))<1e-10

# The current paper uses the saved exponential-allocation fit. Earlier
# benchmarks remain reproducible through --legacy-linear and the archived inputs.
LATEST=ROOT/'02 Research/Unified empirical program 2026-10-23/results/cosmology_final.json'
REGISTER=ROOT/'02 Research/Unified empirical program 2026-10-23/execution_register.json'
EXTENSIONS=ROOT/'02 Research/Manuscript cluster and dynamics integration 2026-10-23/lean_validation_integrated.json'
if not args.legacy_linear:
    latest=json.loads(LATEST.read_text(encoding='utf-8'))
    comp=dict(latest['verification'])
    comp['delta_AIC_conditional_five_vs_six']=comp['delta_AIC_conditional_parameter_counts_5_vs_6']
    geo={'model':'geodesic','allocation':'exponential','parameters':latest['fit_parameters'],
         'parts_higher_accuracy':comp['geodesic'],'Alens':1,'nonlinear':'none',
         'source':str(LATEST.relative_to(ROOT))}
    lcdm={'model':'lcdm','parameters':latest['lcdm_parameters'],
          'parts_higher_accuracy':comp['lcdm'],'Alens':1,'nonlinear':'none'}
    assert abs(comp['delta_chi2']-(comp['geodesic']['total']-comp['lcdm']['total']))<1e-10
    for model in ['geodesic','lcdm']:
        q=comp[model]
        assert abs(q['total']-sum(q[k] for k in ['cmb','bao','sn']))<1e-9

outputs=[HERE/'current_verification.json']+[HERE/'figures'/f'{name}.{ext}'
         for name in ['redshift','cosmology','release_history'] for ext in ['pdf','png']]
existing=[p for p in outputs if p.exists()]
if existing:
    backup=HERE/'Previous PDFs'/datetime.now().strftime('%Y%m%d_%H%M%S_%f_figure_sources')
    for p in existing:
        q=backup/p.relative_to(HERE); q.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(p,q)

plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
    'axes.spines.top':False,'axes.spines.right':False,'axes.titleweight':'bold',
    'savefig.bbox':'tight','pdf.fonttype':42})
BLUE='#183c5a'; TEAL='#127c80'; RED='#b14b3d'; GRAY='#6f7881'
def save(fig,name):
    fig.savefig(HERE/'figures'/f'{name}.pdf')
    fig.savefig(HERE/'figures'/f'{name}.png',dpi=180)
    plt.close(fig)

fig,axs=plt.subplots(1,2,figsize=(10,3.8),gridspec_kw={'width_ratios':[1.5,1]})
zz=np.linspace(0,1.6,400)
axs[0].axvspan(.33,1.44,color=GRAY,alpha=.09,label='Published redshift range')
axs[0].plot(zz,a0*np.sqrt(.315*(1+zz)**3+.685),color=TEAL,lw=2.4,label=r'$a_0(0)\,H(z)/H_0$')
axs[0].plot(zz,intercept+slope*zz,color=BLUE,ls='--',label='Uniform-grid linear projection')
axs[0].plot(zz,1.03+1.20*zz,color=RED,lw=1.4,label='Published Appendix E line')
axs[0].scatter([0,0],[a0,intercept],color=[TEAL,BLUE],s=24,zorder=5)
axs[0].set(xlabel='Redshift z',ylabel=r'$a_0$ [$10^{-10}$ m s$^{-2}$]',title='Acceleration and its linear projection')
axs[0].legend(fontsize=8,loc='upper left')
axs[1].errorbar([0,1],[1.03,1.20],yerr=[.05,.10],fmt='o',color=RED,capsize=4,label='Published marginal errors')
axs[1].scatter([0,1],[intercept,slope],marker='D',color=TEAL,s=45,label='Calculated projection',zorder=4)
axs[1].set_xticks([0,1],['Intercept','Slope']); axs[1].set_ylim(.9,1.36)
axs[1].set(ylabel=r'Units of $10^{-10}$ m s$^{-2}$',title='Coefficient comparison')
axs[1].legend(fontsize=8,loc='lower right'); fig.tight_layout(); save(fig,'redshift')

fig,axs=plt.subplots(1,2,figsize=(10,3.7),gridspec_kw={'width_ratios':[1.1,1]})
delta=comp['delta_chi2']
axs[0].barh([1,0],[0,delta],color=[GRAY,TEAL],height=.5)
axs[0].axvline(0,color=GRAY,lw=1)
axs[0].set_yticks([1,0],['LCDM (6)','Geodesic release (5)'])
axs[0].set(xlim=(-.7,.22),ylim=(-.6,1.6),xlabel=r'$\Delta\chi^2$ relative to LCDM',title='Matched linear lensing')
axs[0].text(.025,1,'0',va='center',fontsize=9)
axs[0].text(delta-.025,0,f'{delta:.3f}',va='center',ha='right',fontsize=9)
axs[0].text(.5,.95,r'$A_L=1$ in both models',transform=axs[0].transAxes,ha='center',va='top',fontsize=8)
axs[1].axhline(94.2,color=BLUE,lw=1.5,label='Archived PPF reference target')
axs[1].errorbar([12,14,17],[108.95,94.9,75.65],yerr=[.95,1.8,.25],fmt='o',color=TEAL,capsize=5,label='Partition range')
axs[1].set(xlim=(11,18),ylim=(53,117),xticks=[12,14,17],xlabel='Imposed retention gate [km/s]',
           ylabel=r'$I_{\rm rel}=\int a^{-3}\,dF_{\rm rel}$',title='Hydrodynamic normalization test')
axs[1].legend(fontsize=7.5,loc='lower left'); fig.tight_layout(); save(fig,'cosmology')

# Plot the current allocation, retaining the historical branch on explicit request.
zoom=json.loads(paths[-1].read_text().splitlines()[0])
Ftab=np.load(paths[-2]); zgrid=np.round(np.arange(30,-1e-9,-.01),4)
mix=zoom['params'][1]; i=int(mix/.05); weight=(mix-.05*i)/.05
Fr=(1-weight)*Ftab[i]+weight*Ftab[i+1]
LA=np.linspace(np.log(1e-9),0,3000); A=np.exp(LA); zA=1/A-1
F=np.interp(-zA,-zgrid,Fr,left=0.,right=Fr[-1]); F[zA>30]=0
I=cumulative_trapezoid(np.gradient(F,LA)/A**3,LA,initial=0)
eta=archive['micro']['eta']; wh=zoom['wc']; wb=zoom['params'][0]
wr=2.4728e-5*(1+.2271*3.044); wL=eta*wh*I
Hnorm=np.sqrt(wr/A**4+(wb+wh*(1-eta*F))/A**3+wL)
assert abs(I[-1]-archive['cosmology']['current_background_reintegration']['Irel'])<1e-8
rhoM=(wb+wh*(1-eta*F))/A**3
history_title='Archived linear-depletion history'
if not args.legacy_linear:
    wb,mix=latest['fit_parameters'][:2];wh=5.333*wb
    i=int(mix/.05);weight=(mix-.05*i)/.05
    Fr=(1-weight)*Ftab[i]+weight*Ftab[i+1]
    curve=PchipInterpolator(-np.log1p(zgrid),Fr,extrapolate=False)
    LA=np.linspace(np.log(1e-9),0,30000);A=np.exp(LA);zA=1/A-1
    active=LA>=-np.log(31)
    F=np.zeros_like(LA);dF=np.zeros_like(LA)
    F[active]=curve(LA[active]);dF[active]=curve.derivative()(LA[active])
    stock=wh*np.exp(-eta*F)/A**3
    wL=cumulative_trapezoid(eta*stock*dF,LA,initial=0)
    I=wL.copy();rhoM=wb/A**3+stock
    Hnorm=np.sqrt(wr/A**4+rhoM+wL)
    history_title='Exponential-allocation history'
    assert abs(100*Hnorm[-1]-latest['background']['H0'])<.002
    assert abs(np.interp(-2,-zA,wL/wL[-1])-latest['background']['vacuum_fraction_z2'])<2e-5
fig,axs=plt.subplots(1,2,figsize=(10,3.5)); sel=zA<15
axs[0].plot(zA[sel],F[sel],color=TEAL,lw=2,label=r'$F_{\rm rel}$: released fraction')
axs[0].plot(zA[sel],I[sel]/I[-1],color=BLUE,lw=2,label=r'$\rho_\Lambda(z)/\rho_\Lambda(0)$')
axs[0].set(xlim=(0,15),ylim=(0,1.03),xlabel='Redshift z',ylabel='Fraction',title=history_title)
axs[0].legend(fontsize=8)
axs[1].plot(zA[sel],wL[sel]/Hnorm[sel]**2,color=BLUE,lw=2,label=r'$\Omega_\Lambda(z)$')
axs[1].plot(zA[sel],rhoM[sel]/Hnorm[sel]**2,color=TEAL,lw=2,label=r'$\Omega_{\rm matter}(z)$')
axs[1].set(xlim=(0,6),ylim=(0,1.03),xlabel='Redshift z',ylabel='Fraction of critical density',title='Accumulation and eventual dominance')
axs[1].legend(fontsize=8); fig.tight_layout(); save(fig,'release_history')

record={'created_utc':datetime.now(timezone.utc).isoformat(),
    'scope':'Arithmetic recalculation and saved-result import; no new simulation, cosmological optimization, or Lean build.',
    'redshift':{'a0_z0_in_1e10':a0,'a0_z1_in_1e10':float(a0*np.sqrt(.315*8+.685)),
                'intercept':float(intercept),'slope':float(slope),'redshift_points':112,
                'intercept_marginal_residual_sigma':float((intercept-1.03)/.05),
                'slope_marginal_residual_sigma':float((slope-1.20)/.1)},
    'matched_linear_lensing':comp,'release_fit':geo,'lcdm_fit':lcdm,
    'clock_checks':checks,'growth_check':growth,
    'model_scope':{'fit':('linear-depletion' if args.legacy_linear else 'exponential-allocation')+' geodesic-clock background; linear lensing, Alens=1',
                   'positive_allocation_likelihood':('archived linear comparison selected' if args.legacy_linear else 'completed; saved exponential fit imported'),
                   'archived_release_history_f':0.282706,'archived_hydro_reference_Irel':94.2},
    'lean':{'commit':'432da8c4a8b169a17146b53e4155d6b37915a12f',
            'saved_axiom_audit':paths[6].read_text(),'saved_citation_audit':paths[7].read_text()},
    'source_hashes':{str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
if not args.legacy_linear:
    record['cross_sector_register']=json.loads(REGISTER.read_text(encoding='utf-8'))
    record['lean']['extensions_standalone']=json.loads(EXTENSIONS.read_text(encoding='utf-8'))
    record['lean']['extensions_pr']='https://github.com/jakechinitz/Entropic-EFT-Lean/pull/4'
    pinned=EXTENSIONS.with_name('pinned_lean_verification.json')
    if pinned.exists():
        record['lean']['extensions_pinned']=json.loads(pinned.read_text(encoding='utf-8'))
        record['source_hashes'][pinned.relative_to(ROOT).as_posix()]=hashlib.sha256(pinned.read_bytes()).hexdigest()
    record['release_history_figure']={'allocation':'exponential','mixing_fraction':mix,
        'H0_quadrature':float(100*Hnorm[-1]),'vacuum_fraction_z2':float(np.interp(-2,-zA,wL/wL[-1])),
        'points':len(LA),'source':'Saved fit parameters and Frel_table; background quadrature only'}
    for source in [LATEST,REGISTER,EXTENSIONS]:
        record['source_hashes'][source.relative_to(ROOT).as_posix()]=hashlib.sha256(source.read_bytes()).hexdigest()
    record['scope']='Arithmetic recalculation and saved exponential-fit/result import; no new simulation or cosmological optimization. Standalone Lean checks were rerun during integration; pinned-build status is recorded separately.'
(HERE/'current_verification.json').write_text(json.dumps(record,indent=2),encoding='utf-8')
print(json.dumps({'redshift':record['redshift'],'delta_chi2':delta,'refreshed_figures':['redshift','cosmology','release_history']},indent=2))
