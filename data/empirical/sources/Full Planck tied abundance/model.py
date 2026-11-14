"""Full-likelihood test of the tied abundance.
Models: LCDM; frozen-eta release model with omega_c = r*omega_b (r tied or free).
CMB: Planck 2018 plik_lite TT,TE,EE (l>=30) + two low-l TT bins (planck-lite-py) + lowE tau prior 0.0506 +- 0.0086.
BAO: DESI DR2 (bundle values). SNe: DES-SN5YR or Pantheon+ with the bundle's low-z offset marginalization.
The release background is mapped onto constant CDM plus an effective dark-energy fluid
rho_eff = rho_Lambda(a) - eta*rho_c*F(a)/a^3 (>= 0), passed to CAMB as a PPF w(a) table."""
import os, sys, numpy as np, camb
HERE=os.path.dirname(os.path.abspath(__file__))
DE=os.path.join(HERE,'..','Dark energy prediction tests'); sys.path.insert(0,DE)
sys.path.insert(0,os.path.join(HERE,'planck-lite-py'))
from planck_lite_py import PlanckLitePy
import common
from common import aniso, bgs, c_km, SNe, A, LA, w_r
from test_release import caustic, ETA
_cwd=os.getcwd(); os.chdir(os.path.join(HERE,'planck-lite-py'))
PL=PlanckLitePy(year=2018,spectra='TTTEEE',use_low_ell_bins=True)
os.chdir(_cwd)
TAU=(0.0506,0.0086)
NNU=3.044
ALENS=float(os.environ.get('ALENS','1.0'))

def release_background(wb,wc,sm):
    F,wL,H=caustic(wb,wc,ETA,lambda z: np.full_like(z,sm))
    h=float(H[-1])
    rho_eff=wL-ETA*wc*F/A**3
    return h,F,wL,H,rho_eff

def w_table(rho_eff):
    m=A>=1e-5; a=A[m]; r=rho_eff[m]
    lr=np.log(np.maximum(r,1e-300)); w=-1-np.gradient(lr,np.log(a))/3
    w=np.where(r>1e-12*r[-1],w,-30.0); w=np.clip(w,-30,0)
    # thin the table
    sel=np.unique(np.linspace(0,len(a)-1,600).astype(int))
    return a[sel],w[sel]

def camb_run(wb,wc,h,As,ns,tau,w_tab=None,lmax=2600):
    pars=camb.CAMBparams()
    pars.set_cosmology(H0=100*h,ombh2=wb,omch2=wc,tau=tau,mnu=0.0,nnu=NNU,num_massive_neutrinos=0,Alens=(ALENS if w_tab is not None else 1.0))
    pars.InitPower.set_params(As=As,ns=ns)
    if w_tab is not None:
        de=camb.dark_energy.DarkEnergyPPF(); de.set_w_a_table(w_tab[0],w_tab[1]); pars.DarkEnergy=de
    pars.set_for_lmax(lmax,lens_potential_accuracy=1)
    r=camb.get_results(pars)
    return pars,r

def cmb_chi2(pars,r,tau):
    cl=r.get_cmb_power_spectra(pars,CMB_unit='muK')['total']
    c=-2*PL.loglike(cl[2:2509,0],cl[2:2509,3],cl[2:2509,1],2)
    return c+((tau-TAU[0])/TAU[1])**2

def bao_chi2(r):
    rd=r.get_derived_params()['rdrag']; out=0.0
    for (z,dm,sm,dh,sh,rho) in aniso:
        DM=r.comoving_radial_distance(z); DH=c_km/r.hubble_parameter(z)
        r1=(dm-DM/rd)/sm; r2=(dh-DH/rd)/sh
        out+=(r1*r1-2*rho*r1*r2+r2*r2)/(1-rho*rho)
    z,dv,sv=bgs; DM=r.comoving_radial_distance(z); DH=c_km/r.hubble_parameter(z)
    out+=((dv-(z*DM*DM*DH)**(1/3)/rd)/sv)**2
    return out

_SN={}
def sn_chi2(r,which,offset=True):
    if which not in _SN: _SN[which]=SNe(which)
    S=_SN[which]
    dm=r.comoving_radial_distance(S.z)
    res=S.mb-(5*np.log10((1+S.zh)*dm)+25)
    if offset:
        v=np.array([S.one@res,S.CW@res]); return float(res@(S.C@res)-v@S.G2i@v)
    return float(res@(S.C@res)-(S.one@res)**2/S.oo)

def total(model,p,data):
    """model: 'lcdm' p=(wb,wc,h,lnAs,ns,tau); 'tied' p=(wb,sm,lnAs,ns,tau) with r=data['r']; 'free' p=(wb,wc,sm,lnAs,ns,tau)."""
    if model=='lcdm':
        wb,wc,h,lnAs,ns,tau=p; wtab=None
    elif model=='tied':
        wb,sm,lnAs,ns,tau=p; wc=data['r']*wb
        h,F,wL,H,rho=release_background(wb,wc,sm); wtab=w_table(rho)
    else:
        wb,wc,sm,lnAs,ns,tau=p
        h,F,wL,H,rho=release_background(wb,wc,sm); wtab=w_table(rho)
    if not(0.018<wb<0.027 and 0.09<wc<0.15 and 0.6<h<0.8 and 0.01<tau<0.12): return 1e9,{}
    pars,r=camb_run(wb,wc,h,np.exp(lnAs)/1e10,ns,tau,wtab)
    parts={'cmb':cmb_chi2(pars,r,tau)}
    if data.get('bao'): parts['bao']=bao_chi2(r)
    if data.get('sn'): parts['sn']=sn_chi2(r,data['sn'])
    return sum(parts.values()),dict(parts=parts,h=h,wc=wc,ratio=wc/wb)
