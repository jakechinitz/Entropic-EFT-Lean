"""Reproduce arithmetic and archived-output likelihoods for the empirical review.
Run with numpy, scipy and matplotlib from this workspace. No N-body runs are launched.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, itertools, json, math, re, zipfile, shutil, runpy
from datetime import datetime
import numpy as np
from scipy.optimize import brentq
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
DEFAULT_WORKSPACE=next((p for p in HERE.parents
    if (p/'.organization/file_locations.csv').is_file()), HERE.parents[2])
parser.add_argument('--workspace',type=Path,default=DEFAULT_WORKSPACE)
ROOT=parser.parse_args().workspace.resolve()
# Preserve all previous numerical records and figure versions before reproduction.
prior_outputs=[HERE/'numerical_review.json',HERE/'current_verification.json']
prior_outputs += list((HERE/'figures').glob('*'))
backup=HERE/'Previous PDFs'/datetime.now().strftime('%Y%m%d_%H%M%S_%f_before_reproduction')
for previous in prior_outputs:
    if previous.is_file():
        retained=backup/previous.relative_to(HERE)
        retained.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(previous,retained)
# Resolve the original source keys through the move manifest when available.
import csv
location_index=ROOT/'.organization/file_locations.csv'
if location_index.is_file():
    with location_index.open(encoding='utf-8-sig',newline='') as location_file:
        SOURCE_LOCATIONS={row['original']:row['organized'] for row in csv.DictReader(location_file)}
else:
    SOURCE_LOCATIONS={}
def workspace_file(relative):
    return ROOT / SOURCE_LOCATIONS.get(str(relative).replace('\\','/'), str(relative))
FIG=HERE/'figures'; FIG.mkdir(exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,
 'axes.spines.right':False,'axes.titleweight':'bold','savefig.bbox':'tight','pdf.fonttype':42})
BLUE='#183c5a'; TEAL='#127c80'; RED='#b14b3d'; GOLD='#b88722'; GRAY='#6f7881'
out={}
def imp(name,path):
    spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m); return m
def save(fig,name):
    fig.savefig(FIG/(name+'.pdf')); fig.savefig(FIG/(name+'.png'),dpi=180); plt.close(fig)

# Exact finite ensemble, including the two orientation copies.
m=np.array(list(itertools.permutations(range(-3,4),4)),dtype=float)
k=48-(m.sum(1)**2-(m*m).sum(1))/3; k=np.repeat(k,2)
def moment(e):
    p=np.exp(-e*k); p/=p.sum(); return p@k
eta=brentq(lambda e:e*moment(e)-1.5,.02,.04,xtol=1e-15)
p=np.exp(-eta*k); p/=p.sum(); g=-np.dot(p,np.log(p)); eps=g/(4*np.pi**2)
c=299792458.; Mpc=3.085677581491367e22
a0=eps*c*67400/Mpc
out['micro']={'states':len(k),'eta':eta,'mean_K2':moment(eta),'g':g,'epsilon':eps,'inverse_epsilon':1/eps,'a0_SI':a0}
z=np.round(np.arange(.33,1.44001,.01),2)
y=1.231*np.sqrt(.315*(1+z)**3+.685)
slope,intercept=np.polyfit(z,y,1)
out['redshift']={'range':[.33,1.44],'grid_spacing':.01,'intercept':intercept,'slope':slope,
 'a0_z1_in_1e10':1.231*np.sqrt(.315*8+.685),
 'intercept_marginal_residual_sigma':(intercept-1.03)/.05,'slope_marginal_residual_sigma':(slope-1.20)/.10}
fig,axs=plt.subplots(1,2,figsize=(10,3.8),gridspec_kw={'width_ratios':[1.5,1]})
zz=np.linspace(0,1.6,400); curve=1.231*np.sqrt(.315*(1+zz)**3+.685)
axs[0].axvspan(.33,1.44,color=GRAY,alpha=.09,label='Published redshift range')
axs[0].plot(zz,curve,color=TEAL,lw=2.4,label=r'$1.231\,H(z)/H_0$')
axs[0].plot(zz,intercept+slope*zz,color=BLUE,ls='--',label='Uniform-grid linear projection')
axs[0].plot(zz,1.03+1.20*zz,color=RED,lw=1.4,label='Published Appendix E line')
axs[0].scatter([0,0],[1.231,intercept],color=[TEAL,BLUE],s=24,zorder=5)
axs[0].set(xlabel='Redshift z',ylabel=r'$a_0$ [$10^{-10}$ m s$^{-2}$]',title='A curved prediction, a linear summary')
axs[0].legend(fontsize=8,loc='upper left')
axs[1].errorbar([0,1],[1.03,1.20],yerr=[.05,.10],fmt='o',color=RED,capsize=4,label='Published marginal errors')
axs[1].scatter([0,1],[intercept,slope],marker='D',color=TEAL,s=45,label='Calculated projection',zorder=4)
axs[1].set_xticks([0,1],['Intercept','Slope']); axs[1].set_ylim(.9,1.36)
axs[1].set(ylabel=r'Units of $10^{-10}$ m s$^{-2}$',title='Coefficient comparison')
axs[1].legend(fontsize=8,loc='lower right'); fig.tight_layout(); save(fig,'redshift')

# LMC formula and the original QUMOND flux implementation.
G=4.30091e-6; a0astro=1.231e-10*3.085677581e19/1e6; Mb=3e9
rM=np.sqrt(G*Mb/a0astro)
mass=lambda r:Mb/(-np.expm1(-rM/np.asarray(r)))
q=imp('qumond_review',workspace_file('LMC and satellites checks/qumond_flux.py'))
u=np.array([-1.1,-41.1,-27.9]); u=u/np.linalg.norm(u)*50
flux={name:float(q.dM_lmc(nu,u,30)) for name,nu in q.nus.items()}
out['LMC']={'rM_kpc':rM,'mass30':float(mass(30)),'mass50':float(mass(50)),
 'cap_radius_kpc':float(-rM/np.log(1-1/34)),'qumond_mass30':flux}
fig,axs=plt.subplots(1,2,figsize=(10,3.8),gridspec_kw={'width_ratios':[1.55,1]})
rr=np.linspace(2,70,300); mm=np.minimum(mass(rr),34*Mb)
axs[0].plot(rr,mm/1e10,color=TEAL,lw=2.5,label='Retained profile; stated cap')
axs[0].errorbar(30,4.9,yerr=.2,fmt='o',color=BLUE,capsize=4,label='Warren et al. range')
axs[0].errorbar(50,8.76,yerr=np.array([[1.77],[1.94]]),fmt='s',color=RED,capsize=4,label='Brooks et al. inference')
axs[0].axhline(10.2,color=GRAY,ls=':',lw=1)
axs[0].set(xlabel='Radius [kpc]',ylabel=r'$M(<r)$ [$10^{10} M_\odot$]',title='LMC enclosed gravitational mass')
axs[0].legend(fontsize=8)
vals=[mass(30)/1e10,*[v/1e10 for v in flux.values()]]
axs[1].barh(range(4),vals,color=[TEAL,GRAY,GRAY,GRAY]); axs[1].axvspan(4.7,5.1,color=BLUE,alpha=.16)
axs[1].set_yticks(range(4),['Stock','QUMOND: RAR','QUMOND: simple','QUMOND: standard'],fontsize=8)
axs[1].invert_yaxis(); axs[1].set(xlabel=r'$M(<30\,{\rm kpc})$ [$10^{10} M_\odot$]',title='External-field comparison')
fig.tight_layout(); save(fig,'lmc')

# Recompute the existing evidence from ZIP output objects, without modifying them.
ag=imp('analysis_review',workspace_file('Crater II and Antlia 2 vs LCDM/analyse_grid.py'))
def objects(archive):
    with zipfile.ZipFile(archive) as z:
        return [(n,json.loads(z.read(n))) for n in z.namelist() if n.endswith('.json')]
lmc=objects(workspace_file('Crater II and Antlia 2 vs LCDM/lmc_results.zip'))
def zl(dw,model,s=.3):
    D=ag.DATA[dw]; groups={}
    for fn,d in lmc:
        name=Path(fn).name
        if not name.startswith(dw+'_'+model+'_') or 'cfg' not in d:continue
        delta=float(name.split('_h')[-1].split('_npc')[0]) if model=='lcdm' else None
        cfg=d['cfg']; ob=d['res'][0]; w=ag.size_prior(cfg['b'],cfg['Mstar'])
        a=groups.setdefault(delta,[0.,0.]); a[0]+=w*ag.like(ob,D);a[1]+=w
    if model=='stock':return groups[None][0]/groups[None][1]
    return sum(np.exp(-.5*(d/s)**2)/(s*np.sqrt(2*np.pi))*(.6 if dw=='CraterII' else .3)*a[0]/a[1] for d,a in groups.items())
bfrows=[]
for error in [.1,.2,.3]:
    ag.MODERR=error
    zsl=zl('CraterII','stock')
    row={'model_error':error,
         'LMC_0.3':zsl/zl('CraterII','lcdm',.3),'LMC_0.5':zsl/zl('CraterII','lcdm',.5)}
    bfrows.append(row)
out['CraterII_Bayes_factors']=bfrows
fig,axs=plt.subplots(1,2,figsize=(10,3.9),gridspec_kw={'width_ratios':[1.2,1]})
axs[0].axvspan(.982,1.150,color=GRAY,alpha=.12);axs[0].axhspan(2.4,3.0,color=GRAY,alpha=.12)
axs[0].errorbar(1.066,2.7,xerr=.084,yerr=.3,color='black',fmt='*',markersize=10,capsize=3,label='Adopted comparison data')
for x,y,label,marker,col in [(.86,2.36,'Stock: highest likelihood','D',TEAL),(1.24,2.18,'Stock: next candidate','o',TEAL),(.78,3.46,'NFW: highest likelihood','s',RED)]:
    axs[0].scatter(x,y,label=label,marker=marker,color=col,s=35)
axs[0].set(xlim=(.68,1.33),ylim=(1.7,4.1),xlabel=r'$R_h$ [kpc]',ylabel=r'$\sigma_{\rm los}$ [km s$^{-1}$]',title='Joint size and dispersion test')
axs[0].legend(fontsize=7.3,loc='upper right')
for key,label,col,ls in [('LMC_0.3','With LMC, 0.3 dex',TEAL,'-'),('LMC_0.5','With LMC, 0.5 dex',RED,'--')]:
    axs[1].semilogy([10,20,30],[r[key] for r in bfrows],marker='o',color=col,ls=ls,label=label)
axs[1].set(xlabel='Assumed fractional model error [%]',ylabel='Bayes factor: stock / tested NFW',title='Evidence depends on model error')
axs[1].set_xticks([10,20,30]);axs[1].legend(fontsize=7.5);fig.tight_layout();save(fig,'crater')

# Latest cosmology likelihood and physical-kernel comparison, directly from saved outputs.
zoom=[json.loads(x) for x in (workspace_file('Release zoom/zoom_fits.jsonl')).read_text().splitlines()]
out['cosmology']={'mixing_PBD':zoom[0]}
fig,axs=plt.subplots(1,2,figsize=(10,3.7),gridspec_kw={'width_ratios':[1.1,1]})
labels=['LCDM (6)','Mixing, f fitted (5)','Mixing, f=0.5 (4)','Mixing, f=0.75 (4)']
delta=[0,2227.329-2226.77,2272.638-2226.77,2416.39-2226.77]
axs[0].barh(range(4),np.array(delta)+1e-3,color=[GRAY,TEAL,GOLD,RED]);axs[0].invert_yaxis()
axs[0].set_yticks(range(4),labels,fontsize=8);axs[0].set_xscale('symlog',linthresh=1)
axs[0].set(xlabel=r'$\Delta\chi^2$ relative to LCDM',title='Current mixing-history comparison')
for i,d in enumerate(delta):axs[0].text(max(d,0.02)+.05,i,f'{d:.2f}',va='center',fontsize=8)
axs[1].axhline(94.2,color=BLUE,lw=1.5,label='Integral required by fitted likelihood')
axs[1].errorbar([12,14,17],[108.95,94.9,75.65],yerr=[.95,1.8,.25],fmt='o',color=TEAL,capsize=5,label='Three coarse-partition results (range)')
axs[1].set(xlim=(11,18),ylim=(53,117),xticks=[12,14,17],xlabel='Imposed retention gate [km/s]',ylabel=r'$I_{\rm rel}=\int a^{-3}\,dF_{\rm rel}$',title='First hydrodynamic run')
axs[1].legend(fontsize=7.5,loc='lower left');fig.tight_layout();save(fig,'cosmology')

# Integrate the saved mixing table at the current fitted f, on the likelihood grid.
from scipy.integrate import cumulative_trapezoid
Ftab=np.load(workspace_file('Release zoom/Frel_table.npy')); zgrid=np.round(np.arange(30,-1e-9,-.01),4)
f=zoom[0]['params'][1]; i=int(f/.05); w=(f-.05*i)/.05
Fr=(1-w)*Ftab[i]+w*Ftab[i+1]
LA=np.linspace(np.log(1e-9),0,3000); A=np.exp(LA); zA=1/A-1
F=np.interp(-zA,-zgrid,Fr,left=0.,right=Fr[-1]); F[zA>30]=0
I=cumulative_trapezoid(np.gradient(F,LA)/A**3,LA,initial=0)
wh=zoom[0]['wc']; wb=zoom[0]['params'][0]; wr=2.4728e-5*(1+.2271*3.044)
wL=eta*wh*I; Hnorm=np.sqrt(wr/A**4+(wb+wh*(1-eta*F))/A**3+wL)
out['cosmology']['current_background_reintegration']={'Frel0':float(F[-1]),'Irel':float(I[-1]),
 'h':float(Hnorm[-1]),'OmegaLambda':float(wL[-1]/Hnorm[-1]**2),
 'z_half':float(np.interp(.5,I/I[-1],zA)),'fraction_by_z6':float(np.interp(-6,-zA,I/I[-1]))}
fig,axs=plt.subplots(1,2,figsize=(10,3.5)); sel=zA<15
axs[0].plot(zA[sel],F[sel],color=TEAL,lw=2,label=r'$F_{\rm rel}$: released fraction')
axs[0].plot(zA[sel],I[sel]/I[-1],color=BLUE,lw=2,label=r'$\rho_\Lambda(z)/\rho_\Lambda(0)$')
axs[0].set(xlim=(0,15),ylim=(0,1.03),xlabel='Redshift z',ylabel='Fraction',title='Archived linear-depletion history')
axs[0].legend(fontsize=8)
rhoM=(wb+wh*(1-eta*F))/A**3
axs[1].plot(zA[sel],wL[sel]/Hnorm[sel]**2,color=BLUE,lw=2,label=r'$\Omega_\Lambda(z)$')
axs[1].plot(zA[sel],rhoM[sel]/Hnorm[sel]**2,color=TEAL,lw=2,label=r'$\Omega_{\rm matter}(z)$')
axs[1].set(xlim=(0,6),ylim=(0,1.03),xlabel='Redshift z',ylabel='Fraction of critical density',title='Accumulation and eventual dominance')
axs[1].legend(fontsize=8);fig.tight_layout();save(fig,'release_history')

files=['Astra Quantum gravity completion.tex','Spacetime consolidation 2026-10-16/MICROSTRUCTURE_TO_SPACETIME.md',
 'llm writing guide.docx','caustic_fit_bundle_v3.zip','Crater II and Antlia 2 vs LCDM/PREREGISTRATION.md',
 'Crater II and Antlia 2 vs LCDM/grid_results.zip','Crater II and Antlia 2 vs LCDM/lmc_results.zip',
 'Full Planck tied abundance/fits_lenscorr.jsonl','Release zoom/RESULTS.md','Release zoom/zoom_fits.jsonl']
out['sha256']={f:hashlib.sha256(workspace_file(f).read_bytes()).hexdigest() for f in files}
(HERE/'numerical_review.json').write_text(json.dumps(out,indent=2),encoding='utf8')
print(json.dumps(out,indent=2))
# Apply the current precision and matched-fit supplement after the historical review.
runpy.run_path(str(HERE/'refresh_verified_results.py'),run_name='__main__')
