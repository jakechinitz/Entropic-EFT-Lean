import numpy as np
G=4.30091e-6                       # kpc (km/s)^2 / Msun
a0=1.231e-10*3.085677581e19/1e6    # (km/s)^2/kpc
nus={
 'exponential (RAR)': lambda y: 1.0/(1.0-np.exp(-np.sqrt(y))),
 'simple':            lambda y: 0.5+np.sqrt(0.25+1.0/y),
 'standard':          lambda y: np.sqrt(0.5+np.sqrt(0.25+1.0/y**2)),
}
# Newtonian fields (vector acceleration, pointing toward mass), positions in kpc
def g_plummer(x,M,b,c):
    d=x-c; r2=(d**2).sum(-1)+b*b
    return -G*M*d/r2[...,None]**1.5
def g_hernquist(x,M,a,c):
    d=x-c; r=np.sqrt((d**2).sum(-1))
    return -G*M*d/(r*(r+a)**2)[...,None]
def g_mn(x,M,a,b,c):
    d=x-c; R2=d[...,0]**2+d[...,1]**2; z=d[...,2]; s=np.sqrt(z*z+b*b)
    D=(R2+(a+s)**2)**1.5
    gx=-G*M*d[...,0]/D; gy=-G*M*d[...,1]/D; gz=-G*M*z*(a+s)/(s*D)
    return np.stack([gx,gy,gz],-1)
O=np.zeros(3)
def g_MW(x, Mb=6e10):
    fb=1e10/6e10
    return g_hernquist(x,fb*Mb,0.6,O)+g_mn(x,(1-fb)*Mb,3.0,0.28,O)
def g_LMC(x,cL,ML=3e9): return g_plummer(x,ML,1.5,cL)
# sphere quadrature
mu,wmu=np.polynomial.legendre.leggauss(96); nph=192
ph=np.linspace(0,2*np.pi,nph,endpoint=False); wph=2*np.pi/nph
st=np.sqrt(1-mu**2)
nhat=np.stack([st[:,None]*np.cos(ph)[None,:], st[:,None]*np.sin(ph)[None,:], np.repeat(mu[:,None],nph,1)],-1)
W=wmu[:,None]*wph*np.ones((1,nph))
def flux_mass(field, c, r):
    x=c+r*nhat
    F=field(x)
    return -(r*r)*(W*(F*nhat).sum(-1)).sum()/(4*np.pi*G)
def dM_lmc(nu, cL, r, ML=3e9, Mb=6e10, withMW=True):
    def tot(x):
        gN=g_LMC(x,cL,ML)+(g_MW(x,Mb) if withMW else 0)
        y=np.sqrt((gN**2).sum(-1))/a0
        return nu(y)[...,None]*gN
    def mw(x):
        gN=g_MW(x,Mb); y=np.sqrt((gN**2).sum(-1))/a0
        return nu(y)[...,None]*gN
    m=flux_mass(tot,cL,r)
    if withMW: m-=flux_mass(mw,cL,r)
    return m
if __name__=='__main__':
    cL0=np.array([-1.1,-41.1,-27.9]); dL0=np.linalg.norm(cL0); u=cL0/dL0
    rM=np.sqrt(G*3e9/a0)
    radii=[10,17,20,23,30,35]
    print(f"a0={a0:.1f} (km/s)^2/kpc, r_M={rM:.3f} kpc, LMC at {dL0:.1f} kpc")
    print("retained stock / isolated RAR  M(<r)=Mb/(1-exp(-rM/r)):")
    print("   ", "  ".join(f"{r}:{3e9/(1-np.exp(-rM/r))/1e10:.2f}" for r in radii), " [1e10 Msun]")
    for name,nu in nus.items():
        print(f"\n== {name}")
        iso=[dM_lmc(nu,cL0,r,withMW=False)/1e10 for r in radii]
        print("  isolated LMC (no MW)   ", "  ".join(f"{r}:{m:.2f}" for r,m in zip(radii,iso)))
        for D in [50,70,100,150]:
            cL=u*D
            ms=[dM_lmc(nu,cL,r)/1e10 for r in radii]
            gMW=np.linalg.norm(g_MW(cL[None,:])[0]); ge=np.linalg.norm(nu(np.array([gMW/a0]))*gMW)/a0
            print(f"  LMC at {D:3d} kpc (g_e={ge:.3f} a0)", "  ".join(f"{r}:{m:.2f}" for r,m in zip(radii,ms)))
