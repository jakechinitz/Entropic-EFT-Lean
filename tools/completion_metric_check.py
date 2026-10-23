"""Independent symbolic tensor check, not a Lean proof or numerical simulation.
Compute the Levi-Civita connection and Einstein tensor from the metric.
Do not define a general stress tensor to equal G: test the specified dust-vacuum form.
"""
from pathlib import Path
import sympy as s,json,datetime,hashlib
# Repository copy: writes its report under a temporary directory instead of the Sol and Fable build tree.
import tempfile
OUT=Path(tempfile.gettempdir())/'completion_metric_check'/datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
OUT.mkdir(parents=True,exist_ok=True)
t,r,th,ph=s.symbols('t r theta phi',real=True)
coords=(t,r,th,ph);R=s.Function('R')(t,r);Rr=s.diff(R,r);Rt=s.diff(R,t)
N=s.Function('N')(t)
g=s.diag(-N**2,Rr**2,R**2,R**2*s.sin(th)**2);gi=g.inv()
Gamma={}
for a in range(4):
 for b in range(4):
  for c in range(4):
   Gamma[a,b,c]=s.simplify(sum(gi[a,d]*(s.diff(g[d,c],coords[b])+s.diff(g[d,b],coords[c])-s.diff(g[b,c],coords[d]))/2 for d in range(4)))
Ric=s.zeros(4)
for b in range(4):
 for d in range(4):
  Ric[b,d]=s.simplify(sum(s.diff(Gamma[a,b,d],coords[a])-s.diff(Gamma[a,b,a],coords[d])+sum(Gamma[a,a,c]*Gamma[c,b,d]-Gamma[a,d,c]*Gamma[c,b,a] for c in range(4)) for a in range(4)))
Sc=s.simplify(sum(gi[a,b]*Ric[a,b] for a in range(4) for b in range(4)))
G=s.simplify(Ric-g*Sc/2)
Ht=Rt/(N*R);Hr=s.diff(R,t,r)/(N*Rr)
checks={}
checks['hamiltonian']=s.simplify(G[0,0]/N**2-Ht**2-2*Ht*Hr)==0
checks['radial_pressure']=s.simplify(G[1,1]/Rr**2+2*s.diff(Ht,t)/N+3*Ht**2)==0
checks['angular_pressure']=s.simplify(G[2,2]/R**2+s.diff(Ht,t)/N+s.diff(Hr,t)/N+Ht**2+Hr**2+Ht*Hr)==0
checks['azimuthal_pressure']=s.simplify(G[3,3]-s.sin(th)**2*G[2,2])==0
checks['geodesic_comoving_clock']=all(Gamma[a,0,0]==0 for a in range(1,4))
checks['unit_clock_norm']=s.simplify(g[0,0]/N**2+1)==0
checks['all_off_diagonal_zero']=all(s.simplify(G[a,b])==0 for a in range(4) for b in range(4) if a!=b)
# R = r*A^(2/3), A=u+h*v and B=u+j*v. h is spatially varying, not FLRW.
u,v,up,vp,pot=s.symbols('u v up vp pot',real=True)
h=1-r**2/10;j=1-7*r**2/30;A=u+h*v;B=u+j*v;Ap=up+h*vp;Bp=up+j*vp
checks['radial_integrability']=s.simplify(B-A-s.Rational(2,3)*r*s.diff(A,r))==0
a,b=s.symbols('a b',real=True);ad=pot-a*a;bd=pot-b*b
ht=s.Rational(2,3)*a;hr=b-a/3;htd=s.Rational(2,3)*ad;hrd=bd-ad/3
V=s.Rational(4,3)*pot;rho=s.Rational(4,3)*a*b-V
checks['dust_vacuum_hamiltonian']=s.expand(ht**2+2*ht*hr-rho-V)==0
checks['dust_vacuum_radial']=s.expand(2*htd+3*ht**2-V)==0
checks['dust_vacuum_angular']=s.expand(htd+hrd+ht**2+hr**2+ht*hr-V)==0
# The global candidate uses N=1/H, R=r*exp(s)*(1+h*I)^(2/3).
# Check its radial geometry and the proper-time expansion rates independently.
delta,ii,ee,hh,dust,vac=s.symbols('delta ii ee hh dust vac',real=True)
hg=delta/(1+r);jg=delta*(1+r/3)/(1+r)**2
checks['global_profile_radial_relation']=s.simplify(jg-hg-s.Rational(2,3)*r*s.diff(hg,r))==0
checks['global_volume_factor']=s.simplify((1+hg*ii)+s.Rational(2,3)*r*s.diff(hg,r)*ii-(1+jg*ii))==0
av,dv=s.symbols('av dv',real=True)
pa=1+av*ii;pd=1+dv*ii
ag=3*hh/2+av*ee/pa;bg=3*hh/2+dv*ee/pd
D=lambda x:s.diff(x,hh)*(-dust/(2*hh))+s.diff(x,ee)*(-3*ee)+s.diff(x,ii)*(ee/hh)
checks['global_alpha_riccati']=s.factor((hh*D(ag)-s.Rational(3,4)*vac+ag**2).subs(vac,3*hh**2-dust))==0
checks['global_beta_riccati']=s.factor((hh*D(bg)-s.Rational(3,4)*vac+bg**2).subs(vac,3*hh**2-dust))==0
checks['global_volume_evolution']=s.factor(hh*D(pa*pd/ee)-(ag+bg)*pa*pd/ee)==0
checks['global_transverse_rate']=s.factor(hh*(1+s.Rational(2,3)*av*ee/(hh*pa))-s.Rational(2,3)*ag)==0
checks['global_radial_rate']=s.factor(hh*(1+dv*ee/(hh*pd)-av*ee/(3*hh*pa))-(bg-ag/3))==0
report={'success':all(checks.values()),'checks':checks,'metric':'diag(-N(t)^2, R_r^2, R^2, R^2 sin(theta)^2), N>0','units':'c=8*pi*G=1','domain':'r>0,0<theta<pi,R>0,R_r>0; local example N=1; global example N=1/H, s>=0 and small positive radial amplitude','limitation':'SymPy validates the differential-geometric reduction; Lean validates the instantiated scalar equations, not the tensor calculation.','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(OUT/'einstein_tensor.txt').write_text(str(G),encoding='utf-8')
(OUT/'verification.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps(report,indent=2));print(OUT)
assert report['success']
