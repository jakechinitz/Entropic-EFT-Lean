from pathlib import Path
import json,sys
import numpy as np
from scipy.integrate import cumulative_trapezoid
from datetime import datetime
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source_snapshot'))
import conservative_gravity as CG
import descent3 as D
from evolve import init

def main():
    x,v,rg,mb,meta=init('A1795',2000,1);m=meta['total_stock_Msun']/len(x)
    pb=CG.baryon_potential(rg,mb);h=1e-3
    errs=[]
    cached_errors=[]
    for softening in [0.,2.5,5.]:
        vv=np.zeros_like(v);CG.kick(x,vv,rg,pb,m,h,softening)
        F=m*vv/(CG.C*h)
        rr=np.linalg.norm(x,axis=1)
        aa=CG.radial_coefficients(rr,np.argsort(rr),rg,pb,m,softening)
        cached=np.zeros_like(v);CG.kick_cached(x,cached,aa,h)
        cached_errors.append(float(np.max(abs(cached-vv))))
        for i in [0,17,151,501,1999]:
            for k in range(3):
                dx=1e-3;xp=x.copy();xm=x.copy();xp[i,k]+=dx;xm[i,k]-=dx
                fd=-(CG.energy(xp,v,m,rg,pb,softening)-CG.energy(xm,v,m,rg,pb,softening))/(2*dx)
                errs.append(abs(fd-F[i,k])/max(abs(F[i,k]),1))
    assert max(errs)<1e-4,errs
    a=CG.energy(x,v,m,rg,pb);b=D.stock_energy(x,v,m,rg,mb)
    assert abs(a/b-1)<1e-12
    # Central impulse algebra and debit are checked independently of acceptance.
    rng=np.random.default_rng(88);de=[];dp=[];dl=[]
    for _ in range(200):
        xx=rng.normal(size=(2,3));vv=rng.normal(size=(2,3));axis=xx[0]-xx[1];axis/=np.linalg.norm(axis)
        w=float((vv[0]-vv[1])@axis);dw=rng.normal();new=vv.copy();new[0]+=.5*dw*axis;new[1]-=.5*dw*axis
        debit=.25*((w+dw)**2-w*w)
        de.append(abs(.5*np.sum(new*new-vv*vv)-debit))
        dp.append(np.max(abs(new.sum(0)-vv.sum(0))))
        dl.append(np.max(abs(np.cross(xx,new).sum(0)-np.cross(xx,vv).sum(0))))
    assert max(de+dp+dl)<1e-13
    assert max(cached_errors)<1e-12
    result=dict(force_is_energy_gradient_max_relative_error=max(errs),tested_softening_kpc=[0,2.5,5],maximum_cached_kick_difference=max(cached_errors),same_initial_energy_as_archived_relative_error=abs(a/b-1),contact_debit_max_abs_error=max(de),contact_momentum_max_abs_error=max(dp),contact_angular_momentum_max_abs_error=max(dl),status='PASS')
    out=HERE/('numerical_checks_'+datetime.now().strftime('%Y%m%d_%H%M%S')+'.json');out.write_text(json.dumps(result,indent=2));print(result)

if __name__=='__main__':main()
