"""Independent checks of pair forces, hydro work, reciprocal contact, units."""
from pathlib import Path
import json,hashlib,datetime
import numpy as np
import merger as s
HERE=Path(__file__).resolve().parent
rng=np.random.default_rng(37717)
x=rng.normal(size=(50,3));v=rng.normal(size=(50,3));m=rng.uniform(.1,2,size=50);u=rng.uniform(.1,1,size=50)
a,phi=s.gravity(x,m,.1)
dr=x[:,None,:]-x[None,:,:];d2=np.sum(dr*dr,axis=2)+.01;np.fill_diagonal(d2,np.inf)
ar=-np.sum(m[None,:,None]*dr/d2[:,:,None]**1.5,axis=1);pr=-np.sum(m[None,:]/np.sqrt(d2),axis=1)
assert np.max(abs(a-ar))<1e-12 and np.max(abs(phi-pr))<1e-12
rho=s.density(x,m,.6);ah,du=s.hydro(x,v,m,u,rho,.6)
hydro_power=np.sum(m[:,None]*v*ah)+m@du
assert abs(hydro_power)<1e-10
assert np.linalg.norm(np.sum(m[:,None]*ah,axis=0))<1e-11
assert np.linalg.norm(np.sum(m[:,None]*np.cross(x,ah),axis=0))<1e-11
max_p=max_l=max_e=0.
for _ in range(10000):
    xi,xj=rng.normal(size=(2,3));vi,vj=rng.normal(size=(2,3));mi,mj=np.exp(rng.uniform(-5,2,size=2))
    n=(xi-xj)/np.linalg.norm(xi-xj);old=(vi-vj)@n;new=rng.normal();delta=(new-old)*n
    vin=vi+mj/(mi+mj)*delta;vjn=vj-mi/(mi+mj)*delta
    max_p=max(max_p,np.linalg.norm(mi*(vin-vi)+mj*(vjn-vj)))
    max_l=max(max_l,np.linalg.norm(mi*np.cross(xi,vin-vi)+mj*np.cross(xj,vjn-vj)))
    dE=.5*mi*(vin@vin-vi@vi)+.5*mj*(vjn@vjn-vj@vj)
    exact=.5*mi*mj/(mi+mj)*(new*new-old*old);max_e=max(max_e,abs(dE-exact))
assert max(max_p,max_l,max_e)<1e-11
assert s.speed(1)==0 and s.speed(2.2)>0
# Units are an illustration; they were not used to choose a final map.
G=4.30091e-6;mass_msun=1e15;scale_kpc=300.
velocity=np.sqrt(G*mass_msun/scale_kpc);time_gyr=scale_kpc/velocity*.9777922217
report={'gravity_reference_max_error':float(np.max(abs(a-ar))),
        'hydro_instantaneous_energy_identity_error':float(abs(hydro_power)),
        'pair_momentum_error':float(max_p),'pair_angular_error':float(max_l),'pair_energy_error':float(max_e),
        'zero_floor_gate':True,'unit_mass_Msun':mass_msun,'unit_length_kpc':scale_kpc,
        'unit_velocity_km_s':velocity,'unit_time_Gyr':time_gyr,
        'rate_nu1_per_Gyr':1/time_gyr,'rate_nu01_per_Gyr':.1/time_gyr,
        'conditional_tests_passed':True}
with (HERE/'checks.json').open('x') as f:json.dump(report,f,indent=2)
print(json.dumps(report))
