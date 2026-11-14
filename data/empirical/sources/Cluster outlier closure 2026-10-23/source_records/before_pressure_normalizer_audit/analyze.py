"""Conservative inventory and common-potential audits; no fitted theory amplitude."""
from pathlib import Path
import sys, json, csv, hashlib
import numpy as np
from scipy.optimize import brentq, linprog
from scipy.integrate import cumulative_trapezoid
from scipy.interpolate import PchipInterpolator

HERE=Path(__file__).resolve().parent
PREV=HERE.parent/'Observed cluster tests 2026-10-23'
sys.path.insert(0,str(PREV/'dependencies'));sys.path.insert(0,str(PREV))
from astropy.io import fits
import radial_analysis as old
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
for p in ['results','figures','logs','formalization']: (HERE/p).mkdir(exist_ok=True)
K=old.K;G=old.G_KPC
MU=.60
MP_KEV_KMS2=1.67262192595e-27*1e6/1.602176634e-16
F=lambda x:np.log1p(x)-x/(1+x)
def nfw_pair(l,z):
    ratio=l['M500']/l['M200'];y=(.4*ratio)**(1/3)
    c=brentq(lambda c:F(c*y)/F(c)-ratio,.1,100)
    return c
def nfw500(m500,c,z):
    y=brentq(lambda y:F(c*y)/F(c)-2.5*y**3,.05,.99)
    r500=(m500/(4*np.pi/3*500*old.critical_density(z)))**(1/3)
    rs=r500/(y*c)
    return lambda r:m500*F(np.asarray(r)/rs)/F(r500/rs),r500
def nfw200(m200,c,z):
    r200=(m200/(4*np.pi/3*200*old.critical_density(z)))**(1/3)
    return lambda r:m200*F(np.asarray(r)/(r200/c))/F(c)
def loginterp(x,y):
    f=PchipInterpolator(np.log(x),np.log(y),extrapolate=False)
    return lambda x:np.exp(f(np.log(x)))
def gas_pressure(c):
    base=PREV/'source_data/xcop'/c
    with fits.open(base/(c+'_density_L1.fits')) as h:
        d=h[1].data;rd=(d['R_IN'].astype(float)+d['R_OUT'])/2
        ne=loginterp(rd,d['NE'])
    with fits.open(base/(c+'_pressure.fits')) as h:
        d=h[1].data;rp=d['RW_X']*h[1].header['R500']
        pe=loginterp(rp,d['P_X']*h[1].header['P500'])
    return ne,pe

lensing=json.loads((PREV/'source_data/lensing_table_A2.json').read_text())['clusters']
report={'k':K,'mu_for_pressure_conversion':MU,
        'scope':'Conditional profile and conservation diagnostics; no joint likelihood or transport selection.',
        'lensing_pressure':{},'inventory':{}}
checks={}
fig,axs=plt.subplots(2,2,figsize=(11,8))
for j,c in enumerate(['A1795','A2029']):
    hd,ma,ga,rg,st=old.profile(c);z=hd['REDSHIFT'];r5=hd['R500']
    mh=old.interp(ma['RADIUS'],ma['M_NFW']);mf=old.interp(ma['RADIUS'],ma['M_FORW'])
    l=lensing[c];c200=nfw_pair(l,z);ne,pe=gas_pressure(c)
    rr=np.geomspace(100,1700,800)
    end=330 if c=='A1795' else 670
    r=np.linspace(100,end,3001)
    rec={'c200_inferred_from_published_pair':c200,'interval_kpc':[100,end], 'scenarios':{}}
    ax=axs[0,j];ax.plot(rr,mh(rr)/1e14,label='X-COP thermal mass',color='#235d85',lw=2)
    ax.plot(rr,mf(rr)/1e14,label='Forward thermal mass',color='#235d85',ls=':')
    for label,mult,dc in [('central',0,0),('mass_minus_1sigma',-1,0),('mass_plus_1sigma',1,0),('lower_concentration',0,-.18),('higher_concentration',0,.18)]:
        m500=(l['M500']+mult*l['eM500'])*1e14
        ml,rwl=nfw500(m500,c200*10**dc,z)
        dm=ml(r)-mh(r)
        integrand=MU*MP_KEV_KMS2*G*ne(r)*dm/r**2
        forward=cumulative_trapezoid(integrand,r,initial=0)
        # At each endpoint s, P_nt(100) >= integral_100^s rho G DeltaM/r^2.
        # Max over s is a necessary bound, without assuming DeltaM positive.
        p0_min=max(0,float(forward.max()))
        cum=forward[-1]-forward
        minimum_boundary=max(0,-float(cum.min()))
        pmin=cum+minimum_boundary
        support=pmin/pe(r)
        q500=float(1-mh(r5)/ml(r5))
        rec['scenarios'][label]={
            'M500_Msun':m500,'c200':c200*10**dc,'R500_kpc':rwl,
            'common_aperture_thermal_bias_at_HSE_R500':q500,
            'minimum_Pnt_over_Pth_at_100kpc':p0_min/float(pe(100)),
            'maximum_minimum_Pnt_over_Pth_in_interval':float(np.max(support)),
            'radius_of_maximum_minimum_support_kpc':float(r[np.argmax(support)]),
            'required_mass_difference_positive_through_interval':bool(np.all(dm>=0)),
            'mass_ratio_at_100kpc':float(ml(100)/mh(100)),
            'mass_ratio_at_XRISM_outer_radius':float(ml(end)/mh(end)),
            'equivalent_sigma_los_lower_bound_kms_at100':float(np.sqrt(p0_min/(MU*MP_KEV_KMS2*ne(100)))),
            'pressure_boundary_electron_equivalent_keV_cm3':minimum_boundary}
        if label=='central':
            rec['contact_targets']=[]
            for R in [end,500,r5]:
                acceleration=G*float(ml(R)-mh(R))/R**2 / 3.085677581491367e13
                rec['contact_targets'].append({'r_kpc':float(R),
                    'outward_acceleration_required_m_s2':acceleration,
                    'fraction_of_total_gravity':float(1-mh(R)/ml(R)),
                    'velocity_change_if_unbalanced_for_500Myr_km_s':acceleration*(500e6*365.25*86400)/1000})
        if label=='central':
            ax.plot(rr,ml(rr)/1e14,label='MENeaCS central NFW target',color='#b65632',lw=2)
            axs[1,j].plot(r,support,label='Central lensing target',color='#b65632',lw=2)
        if label in ['mass_minus_1sigma','mass_plus_1sigma']:
            ax.plot(rr,ml(rr)/1e14,color='#b65632',alpha=.5,ls='--')
            axs[1,j].plot(r,support,color='#b65632',alpha=.5,ls='--',label='Mass +/- quoted error' if mult==-1 else None)
        if label=='lower_concentration':
            axs[1,j].plot(r,support,color='#8b61a0',ls=':',label='Central mass, c lower by 0.18 dex')
        if label=='central':
            checks[c+'_NFW_pair_recovery']=bool(abs(ml((l['M200']*1e14/(4*np.pi/3*200*old.critical_density(z)))**(1/3))/(l['M200']*1e14)-1)<1e-10)
            checks[c+'_pressure_bound_equivalence']=abs(float(pmin[0])-p0_min)<1e-12
            with (HERE/'results'/f'{c}_pressure.csv').open('w',newline='') as f:
                w=csv.writer(f);w.writerow(['r_kpc','M_thermal_Msun','M_lensing_target_Msun','ne_cm-3','Pe_keV_cm-3','minimum_nonthermal_to_thermal_pressure']);w.writerows(zip(r,mh(r),ml(r),ne(r),pe(r),support))
    if c=='A2029':
        xr=nfw200(9.5e14,5.9,z)
        rec['new_XRISM_model']={'M200_Msun':9.5e14,'c200':5.9,
            'new_to_old_mass_at670':float(xr(670)/mh(670)),
            'new_to_old_mass_at_HSE_R500':float(xr(r5)/mh(r5)),
            'MENeaCS_minus_XRISM_M200_in_MENeaCS_sigma':(l['M200']-9.5)/l['eM200']}
        ax.plot(rr,xr(rr)/1e14,color='#4e8761',ls='-.',label='2025 XRISM joint model')
    report['lensing_pressure'][c]=rec
    ax.axvspan(100,end,color='.7',alpha=.1);ax.set_title(c);ax.set_xlabel('Physical radius [kpc]');ax.set_ylabel(r'Enclosed mass [$10^{14} M_\odot$]');ax.set_ylim(bottom=0);ax.legend(fontsize=7)
    axs[1,j].axhline(.02,color='#235d85',ls='-.',label='2% scale (not a global limit)')
    axs[1,j].set_xlabel('Radius [kpc]');axs[1,j].set_ylabel('Minimum $P_{nt}/P_{th}$');axs[1,j].legend(fontsize=7);axs[1,j].set_ylim(bottom=0)
for ax in axs.flat:ax.grid(alpha=.17)
fig.tight_layout();fig.savefig(HERE/'figures/common_potential.png',dpi=180);plt.close(fig)

# A644: exact minimax interval feasibility, not a chi-square with fake covariance.
c='A644';hd,ma,ga,rg,st=old.profile(c);r5=hd['R500']
rr=np.asarray(ma['RADIUS'],float)
sel=(rr>=.1*r5)&(rr<=min(1.5*r5,rg.max(),st['RADIUS'].max()))
r=rr[sel];mb=old.interp(rg,ga['MGAS'])(r)+old.stellar(st,r,r5)
raw=np.asarray(ma['M_FORW'][sel],float);err=np.asarray(ma['EM_FORW'][sel],float)
stock=(raw-mb)/1e14;sig=err/1e14;n=len(r)
# x_i >=0, x_{i+1}>=x_i, |x_i - stock_i| <= t sig_i.
A=[];B=[]
for i in range(n):
    row=np.zeros(n+1);row[i]=1;row[-1]=-sig[i];A.append(row);B.append(stock[i])
    row=np.zeros(n+1);row[i]=-1;row[-1]=-sig[i];A.append(row);B.append(-stock[i])
for i in range(n-1):
    row=np.zeros(n+1);row[i]=1;row[i+1]=-1;A.append(row);B.append(0)
obj=np.zeros(n+1);obj[-1]=1
lp=linprog(obj,A_ub=A,b_ub=B,bounds=[(0,None)]*(n+1),method='highs')
assert lp.success
t=float(lp.x[-1])
# Canonical witness: cumulative max of clipped lower interval bounds.
fixed=np.maximum.accumulate(np.maximum(0,stock-t*sig))
pair=max(((stock[i]-stock[j])/(sig[i]+sig[j]),i,j) for i in range(n) for j in range(i,n))
negative=max(0,float(np.max(-stock/sig)));closed=max(0,pair[0],negative)
checks['minimax_LP_matches_pairwise_formula']=bool(abs(t-closed)<1e-7)
checks['A644_monotone_witness']=bool(np.all(np.diff(fixed)>=-1e-10) and np.all(abs(fixed-stock)<=t*sig+1e-8))
models={}
for model in ['NFW','EIN','ISO','BUR']:
    values=np.asarray(ma['M_'+model][sel],float)-mb
    models[model]={'negative_stock_shells':int((np.diff(values)<0).sum()),'max_deviation_from_forward_in_marginal_sigma':float(np.max(np.abs(ma['M_'+model][sel]-raw)/err))}
report['A644']={'number_of_mass_knots':n,'radius_range_kpc':[float(r[0]),float(r[-1])],
 'negative_forward_total_mass_shells':int((np.diff(raw)<0).sum()),
 'negative_forward_stock_shells':int((np.diff(stock)<0).sum()),
 'minimum_max_marginal_error_displacement':t,
 'limiting_pair_radii_kpc':[float(r[pair[1]]),float(r[pair[2]])],
 'limiting_pair_cumulative_mass_difference_Msun':float((stock[pair[1]]-stock[pair[2]])*1e14),
 'physical_models':models,'interpretation':'Marginal error envelope feasibility only; unknown covariance, no probability or p-value.'}
fig,ax=plt.subplots(figsize=(8,4.4))
ax.errorbar(r,stock,yerr=sig,color='#b65632',fmt='.',alpha=.5,label='Forward required stock +/- marginal error')
ax.plot(r,fixed,color='#4e8761',label=f'Nonnegative-shell witness (max shift {t:.2f} error units)')
for model,col in [('NFW','#235d85'),('BUR','#8b61a0')]:ax.plot(r,(ma['M_'+model][sel]-mb)/1e14,color=col,label=model+' required stock')
ax.set_xlabel('Radius [kpc]');ax.set_ylabel(r'Cumulative stock mass [$10^{14} M_\odot$]');ax.legend(fontsize=8);ax.grid(alpha=.2);fig.tight_layout();fig.savefig(HERE/'figures/A644_admissibility.png',dpi=180);plt.close(fig)
with (HERE/'results/A644_admissibility.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['r_kpc','baryon_Msun','forward_required_stock_Msun','forward_mass_error_Msun','monotone_witness_stock_Msun']);w.writerows(zip(r,mb,stock*1e14,err,fixed*1e14))

# One finite-aperture inventory rule, including both signs of segregation.
# Minimal source cohort B0=max(B,C/k); outside masses are nonnegative.
# Transfer observed cumulative quantiles onto a common finite cohort plus reservoir.
transport_checks=[]
for c in ['A1795','A2029','A644','ZW1215','A2319','A2142','A85']:
    hd,ma,ga,rg,st=old.profile(c);r5=hd['R500'];z=hd['REDSHIFT']
    bm=lambda r:old.interp(rg,ga['MGAS'])(r)+old.stellar(st,r,r5)
    mh=old.interp(ma['RADIUS'],ma['M_NFW'])
    targets=[('HSE',mh,r5)]
    if c in lensing:
        l=lensing[c];ml,rwl=nfw500(l['M500']*1e14,nfw_pair(l,z),z)
        targets.append(('lensing_NFW',ml,rwl))
    records={}
    for label,mt,R in targets:
        b=float(bm(R));stock=float(mt(R)-b);b0=max(b,stock/K)
        bout=b0-b;cout=K*b0-stock;eta=K*b/stock
        # Closed finite bins include unresolved inner bin and outside reservoir.
        edges=np.r_[0,np.geomspace(.1*r5,R,25)]
        bs=np.diff(np.r_[0,bm(edges[1:])]);cs=np.diff(np.r_[0,mt(edges[1:])-bm(edges[1:])])
        s=np.r_[cs/K,cout/K];dest=np.r_[bs,bout]
        # Quantile-overlap transport has source rows and destination columns.
        a=np.r_[0,np.cumsum(s)];d=np.r_[0,np.cumsum(dest)]
        T=np.maximum(0,np.minimum(a[1:,None],d[None,1:])-np.maximum(a[:-1,None],d[None,:-1]))
        residual=max(np.max(abs(T.sum(1)-s)),np.max(abs(T.sum(0)-dest)))/b0
        feasible=bool(np.min(s)>=0 and np.min(dest)>=0 and residual<1e-12)
        transport_checks.append(feasible)
        records[label]={'radius_kpc':float(R),'observed_baryon_Msun':b,'required_stock_Msun':stock,
            'eta':eta,'minimum_initial_cohort_baryon_Msun':b0,'outside_baryon_Msun':bout,
            'outside_stock_Msun':cout,'outside_baryon_fraction_of_initial':bout/b0,
            'outside_stock_fraction_of_initial':cout/(K*b0),
            'transport_nonnegative_with_correct_marginals':feasible,'transport_relative_error':float(residual)}
        np.savez(HERE/'results'/f'{c}_{label}_transport.npz',edges_kpc=edges,source_baryon=s,destination_baryon=dest,transport=T)
    if c=='ZW1215':
        l=lensing[c];R=1000*l['Rap500'];ml,_=nfw500(l['M500']*1e14,nfw_pair(l,z),z)
        records['same_aperture_estimators']={'radius_kpc':R,'NFW_lensing_Msun':float(ml(R)),
          'aperture_lensing_Msun':l['Map500']*1e14,'HSE_Msun':float(mh(R)),
          'NFW_and_aperture_correlated':True}
    report['inventory'][c]=records
checks['all_transport_witnesses_positive_and_conservative']=all(transport_checks)
report['checks']=checks
(HERE/'results/audit.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps(report,indent=2))
assert all(checks.values()),checks
