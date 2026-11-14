"""Likelihood pieces copied verbatim from the public bundle (run_board.py): DESI DR2 BAO + Planck compressed priors + SNe."""
import numpy as np
from scipy.integrate import cumulative_trapezoid
from scipy.special import erfc
B='/tmp/claude-0/-home-claude/ac15ef42-75d9-5f0e-befd-265bb6ebe0ef/scratchpad/de/bundle/bundle/'
c_km=299792.458; w_g=2.4728e-5; w_r=w_g*(1+0.2271*3.044)
aniso=[(0.510,13.588,0.167,21.863,0.425,-0.459),(0.706,17.351,0.177,19.455,0.330,-0.404),
       (0.934,21.576,0.152,17.641,0.193,-0.416),(1.321,27.601,0.318,14.176,0.221,-0.434),
       (1.484,30.512,0.760,12.817,0.516,-0.500),(2.330,38.988,0.531,8.632,0.101,-0.431)]
bgs=(0.295,7.942,0.075)
cmb_mu=np.array([1.7502,301.471,0.02236]); cs=np.array([0.0046,0.090,0.00015])
cor=np.array([[1,0.46,-0.66],[0.46,1,-0.33],[-0.66,-0.33,1]])
ICOV=np.linalg.inv(cor*np.outer(cs,cs))
LA=np.linspace(np.log(1e-9),0,3000); A=np.exp(LA)
ZS,ZD=1089.92,1059.94
def chi2_from(H, wb, wm_early, parts=False):
    integ=1.0/(A*H); I=cumulative_trapezoid(integ,LA,initial=0); chi=(I[-1]-I)*c_km/100.0
    Rb=0.75*(wb/w_g)*A; cs_a=1.0/np.sqrt(3*(1+Rb))
    rs_cum=cumulative_trapezoid(cs_a*integ,LA,initial=0)*c_km/100.0
    DM=lambda z: np.interp(np.log(1/(1+z)),LA,chi); rs=lambda z: np.interp(np.log(1/(1+z)),LA,rs_cum)
    Hz=lambda z: np.interp(np.log(1/(1+z)),LA,H)
    rd=rs(ZD); out={}
    for (z,dm,sm,dh,sh,rho) in aniso:
        tdm=DM(z)/rd; tdh=c_km/100.0/Hz(z)/rd; r1=(dm-tdm)/sm; r2=(dh-tdh)/sh
        out[z]=(r1*r1-2*rho*r1*r2+r2*r2)/(1-rho*rho)
    z,dv,sv=bgs; tdm=DM(z); tdh=c_km/100.0/Hz(z); out[z]=((dv-(z*tdm*tdm*tdh)**(1/3)/rd)/sv)**2
    d=np.array([np.sqrt(wm_early)*DM(ZS)*100/c_km, np.pi*DM(ZS)/rs(ZS), wb])-cmb_mu
    out['cmb']=d@ICOV@d
    return out if parts else sum(out.values())
class SNe:
    def __init__(self, which):
        S=np.load(B+{'pplus':'sne.npz','pplus_hz':'sne_hz.npz','des':'des.npz'}[which])
        self.z,self.zh,self.mb,self.C,self.one,self.oo=S['z'],S['zhel'],S['mb'],S['Cinv'],S['one'],float(S['oo'])
        self.lz=np.log(1/(1+self.z)); low=(self.z<0.1).astype(float); self.CW=self.C@low
        self.G2i=np.linalg.inv(np.array([[self.oo,self.one@low],[self.one@low,low@self.CW]]))
    def chi2(self,H,offset):
        integ=1.0/(A*H); I=cumulative_trapezoid(integ,LA,initial=0); chi=(I[-1]-I)*c_km/100.0
        r=self.mb-(5*np.log10((1+self.zh)*np.interp(self.lz,LA,chi))+25)
        if offset:
            v=np.array([self.one@r,self.CW@r]); return r@(self.C@r)-v@self.G2i@v,(self.G2i@v)[1]
        return r@(self.C@r)-(self.one@r)**2/self.oo,0.0
def H_rhoDE(wb,wc,h,f):
    """Flat model with dark-energy density omega_DE*f(a), f(1)=1."""
    wL=h*h-wb-wc-w_r
    return np.sqrt(w_r/A**4+(wb+wc)/A**3+wL*f), wL
