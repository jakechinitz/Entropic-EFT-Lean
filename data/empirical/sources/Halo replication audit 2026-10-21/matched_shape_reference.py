"""Map published ellipsoidal shape uncertainties into spherical-cut moments.

Uses the prescription of Dillamore & Sanders (2026), eqs. 19-20 / sec. 3.4,
but deterministic angular integration replaces million-particle sampling.
Independent Gaussian p=.81+/- .03, q=.73+/- .02, tilt=25.39+/-3.16 deg.
This reference is generated without using the outcomes of the new runs.
"""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np,json
from scipy.special import roots_legendre
HERE=Path(__file__).resolve().parent

def axes(p,q,lo=6.,hi=60.,order=40):
    mu,wm=roots_legendre(order);phi=(np.arange(order*2)+.5)*2*np.pi/(order*2)
    mm,pp=np.meshgrid(mu,phi,indexing='ij');n=np.array([np.sqrt(1-mm.ravel()**2)*np.cos(pp.ravel()),np.sqrt(1-mm.ravel()**2)*np.sin(pp.ravel()),mm.ravel()])
    wt=np.repeat(wm,order*2)*2*np.pi/(order*2);n2=n*n
    p=np.atleast_1d(p);q=np.atleast_1d(q);res=[]
    b1,b2=11.85,28.33;g1,g2,g3=1.7,3.09,4.58
    for start in range(0,len(p),100):
        k=np.sqrt(n2[0]+n2[1]/p[start:start+100,None]**2+n2[2]/q[start:start+100,None]**2)
        low=lo*k;high=hi*k;integ=np.zeros_like(k)
        for l,h,g,c in [(0.,b1,g1,b1**g1),(b1,b2,g2,b1**g2),(b2,np.inf,g3,b1**g2*b2**(g3-g2))]:
            a=np.maximum(low,l);b=np.minimum(high,h);valid=b>a
            integ+=np.where(valid,c*(np.maximum(b,a)**(5-g)-a**(5-g))/(5-g),0.)
        diag=(integ/k**5*wt)@n2.T
        eig=np.sort(diag,axis=1)
        res.append(np.c_[np.sqrt(eig[:,1]/eig[:,2]),np.sqrt(eig[:,0]/eig[:,2])])
    return np.concatenate(res)

if __name__=='__main__':
    base=axes(.81,.73)[0];fine=axes(.81,.73,order=80)[0]
    assert np.max(abs(base-fine))<2e-6,(base,fine)
    rng=np.random.default_rng(211036);p=rng.normal(.81,.03,1000);q=rng.normal(.73,.02,1000)
    assert np.all((p>0)&(p<1)&(q>0)&(q<1))
    a=axes(p,q);cov=np.cov(a.T)
    out={'source':'https://arxiv.org/html/2510.00095v2#S3.SS4',
         'radial_cut_kpc':[6,60],'ellipsoidal_pq':[.81,.73],
         'fiducial_spherical_cut_pq':fine.tolist(),'mapped_mean_pq':a.mean(0).tolist(),
         'mapped_sigma_pq':a.std(0,ddof=1).tolist(),'mapped_covariance_pq':cov.tolist(),
         'tilt_deg':25.39,'tilt_sigma_deg':3.16,'uncertainty_draws':1000,'seed':211036,
         'quadrature_change_40_to_80':(fine-base).tolist(),
         'qualification':'Fixed profile slopes and breaks; independent Gaussian shape errors as in the cited method. The diagnostic compares the stellar distribution, not the simulated stock inertia axes to a dark-halo density parameter. It is conditional on the parametric stellar target and does not reproduce a full data likelihood.'}
    assert not (HERE/'matched_shape_reference.json').exists()
    (HERE/'matched_shape_reference.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
