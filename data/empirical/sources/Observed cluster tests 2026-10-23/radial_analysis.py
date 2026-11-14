"""Resolved real-cluster constraints. Supplied mass profiles are empirical targets."""
from pathlib import Path
import json, csv, sys
import numpy as np
from astropy.io import fits
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.interpolate import PchipInterpolator
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parent
OUT=ROOT
K=5.1760752079627395
G_KPC=4.30091727003628e-6  # kpc (km/s)^2 / Msun
def critical_density(z):
    return 3*(.07**2)*(.3*(1+z)**3+.7)/(8*np.pi*G_KPC)  # Msun/kpc^3
ALPHA=1.64

def projection_fraction(x):
    """Sphere/cylinder mass for spherical gNFW, dimensionless r/rs."""
    f=lambda t:t**(2-ALPHA)*(1+t)**(ALPHA-3)
    sphere=quad(f,0,x,epsabs=1e-10)[0]
    # Stable 1-sqrt(1-u^2); the outer projected integral converges.
    outer=quad(lambda t:f(t)*(x/t)**2/(1+np.sqrt(max(0,1-(x/t)**2))),x,np.inf,
               epsabs=1e-9)[0]
    return sphere/(sphere+outer)

X500=brentq(lambda x:projection_fraction(x)-.75,.001,100)
gx=np.geomspace(.002,8,700)
GF=PchipInterpolator(np.log(gx),[projection_fraction(X500*x) for x in gx],extrapolate=False)

def interp(x,y):
    return PchipInterpolator(np.asarray(x,dtype=float),np.asarray(y,dtype=float),extrapolate=False)

def profile(c):
    d=ROOT/'source_data/xcop'/c
    with fits.open(d/(c+'_hydro_mass.fits')) as h:
        header=dict(h[1].header); mass=h[1].data.copy()
    with fits.open(d/(c+'_fgas_profile.fits')) as h:
        gas=h[1].data.copy(); rg=gas['RADIUS'].astype(float)*h[1].header['R500']
    fs=d/(c+'_mstar.fits')
    star=None
    if fs.exists():
        with fits.open(fs) as h: star=h[2].data.copy()
    return header,mass,gas,rg,star

def stellar(star,r,r500):
    if star is None: return np.zeros_like(np.asarray(r,dtype=float))
    return interp(star['RADIUS'],star['MSTAR'])(r)*GF(np.log(np.asarray(r)/r500))

def evaluate():
    clusters=sorted(p.parent.name for p in (ROOT/'source_data/xcop').rglob('*hydro_mass.fits'))
    lens=json.loads((ROOT/'source_data/lensing_table_A2.json').read_text())['clusters']
    output={'k_stock_per_cohort_baryon':K,'coextensive_baryon_fraction':1/(1+K),
            'stellar_deprojection':{'alpha':ALPHA,'R500_over_rs':X500,'D_at_R500':projection_fraction(X500)},
            'clusters':{},'lensing':{},'interpretation':'Coextensive shortcut is a restricted hypothesis, not a necessary theory prediction. No complete model likelihood.'}
    fig,axs=plt.subplots(3,4,figsize=(13,9),sharex=True,sharey=True)
    focus,axf=plt.subplots(1,2,figsize=(11,4.1))
    rows=[]
    for ax,c in zip(axs.ravel(),clusters):
        hd,ma,ga,rg,st=profile(c); r5=hd['R500']; z=hd['REDSHIFT']
        gm=interp(rg,ga['MGAS']); nm=interp(ma['RADIUS'],ma['M_NFW'])
        fm=interp(ma['RADIUS'],ma['M_FORW'])
        rmax=min(rg.max(),ma['RADIUS'].max(),1.5*r5)
        if st is not None: rmax=min(rmax,float(st['RADIUS'].max()))
        rmin=max(.1*r5,float(rg.min()),float(ma['RADIUS'].min()))
        r=np.geomspace(rmin,rmax,160); ms=stellar(st,r,r5); mb=gm(r)+ms
        ratio=(1+K)*mb/nm(r); req=nm(r)-mb
        eta=K*mb/req
        # Finite shells, not noisy differentiation at every interpolation knot.
        edges=np.geomspace(rmin,rmax,16)
        mbar_edges=gm(edges)+stellar(st,edges,r5)
        shell_req=np.diff(nm(edges)-mbar_edges)
        shell_forw=np.diff(fm(edges)-mbar_edges)
        rec={'has_stellar_profile':st is not None,'redshift':z,'R500_kpc':r5,
             'radial_range_over_R500':[rmin/r5,rmax/r5],
             'minimum_required_stock_fraction_NFW':float(np.min(req/nm(r))),
             'negative_required_stock_shells_NFW':int(np.sum(shell_req<0)),
             'negative_required_stock_shells_forward':int(np.sum(shell_forw<0)),
             'R500':{}}
        for rr in [.1,.3,.5,1.0]:
            r0=r5*rr; g=float(gm(r0)); s=float(stellar(st,r0,r5)); m=float(nm(r0)); b=g+s
            values={'gas_Msun':g,'star_3D_approx_Msun':s,'M_NFW_Msun':m,
                    'coextensive_to_NFW':(1+K)*b/m,'required_stock_per_present_baryon':m/b-1,
                    'relative_baryon_to_stock_retention':K*b/(m-b)}
            if rr==1:
                values['coextensive_to_NFW_double_stars']=(1+K)*(g+2*s)/m
                values['hydro_M500_header_Msun']=hd['M500']*1e14
                values['hydro_error_header_Msun']=hd['ERR_M500']*1e14
                values['gas_error_lo_Msun']=float(interp(rg,ga['MGAS_LO'])(r0))
                values['gas_error_hi_Msun']=float(interp(rg,ga['MGAS_HI'])(r0))
                rec['R500']=values
            rec[str(rr)+'R500']=values
        output['clusters'][c]=rec
        rows.append(dict(cluster=c,stars_available=st is not None,**rec['R500']))
        ax.plot(r/r5,ratio,lw=1.7,color='#215b85',label='gas + deprojected stars' if st is not None else 'gas only')
        ax.plot(r/r5,(1+K)*mb/fm(r),lw=1.0,color='#b45d32',ls='--',label='forward HSE')
        if st is not None:
            sp=interp(st['RADIUS'],st['MSTAR'])(r)
            ax.fill_between(r/r5,(1+K)*gm(r)/nm(r),(1+K)*(gm(r)+sp)/nm(r),color='#215b85',alpha=.13)
            ax.plot(r/r5,(1+K)*(gm(r)+2*ms)/nm(r),color='#215b85',lw=.8,ls=':')
        ax.axhline(1,color='.3',lw=.7);ax.set_xscale('log');ax.set_title(c+('' if st is not None else ' (gas only)'),fontsize=10)
        ax.grid(alpha=.15);ax.set_ylim(.2,1.65);ax.set_xlim(.1,1.5)
        if c in ['A1795','ZW1215']:
            af=axf[0 if c=='A1795' else 1]
            af.plot(r/r5,eta,label='NFW hydrostatic target',color='#215b85')
            af.plot(r/r5,K*mb/(fm(r)-mb),ls='--',color='#b45d32',label='forward hydrostatic target')
            af.axhline(1,color='.3',lw=.8);af.set_title(c);af.set_xlabel('Radius / hydrostatic R500');af.grid(alpha=.2)
            af.set_xscale('log');af.set_ylim(0,1.4)
        with (OUT/'results'/f'{c}_radial.csv').open('x',newline='') as f:
            w=csv.writer(f);w.writerow(['r_kpc','Mgas_Msun','Mstar_3D_approx_Msun','M_NFW_Msun','M_forward_Msun','Mstock_required_Msun','eta','coextensive_to_NFW'])
            w.writerows(zip(r,gm(r),ms,nm(r),fm(r),req,eta,ratio))
        if c in lens:
            l=lens[c]; critical=critical_density(z)
            factor=4*np.pi/3*500*critical
            radius=lambda m:(m*1e14/factor)**(1/3)
            # Use X-COP redshift for the physical aperture conversion. Published
            # lensing redshifts differ slightly; the largest distance mismatch
            # is about 2% (ZW1215), below its quoted mass uncertainty. We do not
            # pretend to recalibrate the original source-redshift efficiencies.
            def at(m):
                rr=radius(m)
                if rr<rmin or rr>min(float(rg.max()),float(st['RADIUS'].max())): return None
                b=float(gm(rr)+stellar(st,rr,r5))
                return {'radius_kpc':rr,'baryon_Msun':b,'ratio':(1+K)*b/(m*1e14),
                        'eta':K*b/(m*1e14-b)}
            lc={'NFW_at_central_mass':at(l['M500']),
                'NFW_at_mass_minus_1sigma':at(max(.001,l['M500']-l['eM500'])),
                'NFW_at_mass_plus_1sigma':at(l['M500']+l['eM500']),
                'published_NFW_M500_1e14':l['M500'],'published_NFW_error_1e14':l['eM500'],
                'published_aperture_M500_1e14':l['Map500'],
                'published_aperture_radius_kpc':1000*l['Rap500']}
            ap=l['Rap500']*1000
            if ap<=min(float(rg.max()),float(st['RADIUS'].max())):
                b=float(gm(ap)+stellar(st,ap,r5));lc['at_published_aperture']={'baryon_Msun':b,
                    'ratio':(1+K)*b/(l['Map500']*1e14),'eta':K*b/(l['Map500']*1e14-b)}
            # Self-consistent overdensity mass under the fixed coextensive shortcut.
            pred=[]
            for smult in [1,2]:
                balance=lambda rr:(1+K)*(gm(rr)+smult*stellar(st,rr,r5))-factor*rr**3
                hi=min(float(rg.max()),float(st['RADIUS'].max()))
                if balance(rmin)*balance(hi)<0:
                    rp=brentq(balance,rmin,hi);mp=factor*rp**3/1e14
                    pred.append({'stellar_multiplier':smult,'R500_kpc':rp,'M500_1e14':mp,
                                 'central_residual_in_lensing_sigma':(l['M500']-mp)/l['eM500']})
                else: pred.append({'stellar_multiplier':smult,'outside_data_range':True})
            lc['coextensive_prediction']=pred;output['lensing'][c]=lc
    fig.supxlabel('Radius / hydrostatic R500');fig.supylabel('Fixed coextensive mass / reconstructed gravitating mass')
    fig.suptitle('X-COP real profiles: same stock normalization for every cluster',fontsize=14)
    fig.tight_layout(rect=(.02,.02,1,.95));fig.savefig(OUT/'figures/xcop_radial.png',dpi=180);plt.close(fig)
    axf[0].set_ylabel('Required relative baryon / stock retention');axf[1].legend(fontsize=8)
    focus.tight_layout();focus.savefig(OUT/'figures/retention_profiles.png',dpi=180);plt.close(focus)
    with (OUT/'results/xcop_at_R500.csv').open('x',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    (OUT/'results/radial_summary.json').write_text(json.dumps(output,indent=2),encoding='utf-8')
    fig,ax=plt.subplots(figsize=(9,4.5));names=list(output['lensing']);xx=np.arange(len(names))
    for i,c in enumerate(names):
        lc=output['lensing'][c];l=lens[c]
        ax.errorbar(i-.16,l['M500'],yerr=l['eM500'],fmt='o',color='#215b85',capsize=3,label='Independent lensing: NFW' if i==0 else None)
        ax.errorbar(i,l['Map500'],yerr=np.array([[l['eMap_lo']],[l['eMap_hi']]]),fmt='s',color='#b45d32',capsize=3,label='Same lensing: aperture method' if i==0 else None)
        pr=lc['coextensive_prediction'];ax.plot([i+.16,i+.16],[pr[0]['M500_1e14'],pr[1]['M500_1e14']],color='#31846a',lw=4)
        ax.plot(i+.16,pr[0]['M500_1e14'],'_',color='#135240',ms=12,label='Coextensive shortcut; 1-2x stellar mass' if i==0 else None)
    ax.set_xticks(xx,names);ax.set_ylabel('M500 [$10^{14}$ solar masses]');ax.grid(axis='y',alpha=.2)
    ax.legend(fontsize=8);fig.tight_layout();fig.savefig(OUT/'figures/independent_lensing.png',dpi=180);plt.close(fig)
    print('CLUSTER  coext/HSE at R500   eta   shells<0 (NFW,forward)')
    for c,d in output['clusters'].items():
        print(c,round(d['R500']['coextensive_to_NFW'],3),round(d['R500']['relative_baryon_to_stock_retention'],3),d['negative_required_stock_shells_NFW'],d['negative_required_stock_shells_forward'])
    for c,l in output['lensing'].items():print(c,'WL',l['published_NFW_M500_1e14'],'shortcut',l['coextensive_prediction'],'eta',l['NFW_at_central_mass']['eta'])

if __name__=='__main__':
    if len(sys.argv)>1:
        OUT=Path(sys.argv[1]).resolve()
        (OUT/'results').mkdir(parents=True,exist_ok=False)
        (OUT/'figures').mkdir(exist_ok=False)
    evaluate()
