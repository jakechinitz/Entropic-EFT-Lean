"""Independent symbolic metric-to-Einstein reduction for the beam witness."""
from pathlib import Path
import datetime,json,shutil
import sympy as s
HERE=Path(__file__).resolve().parent
# Repository copy: writes its report under a temporary directory.
import tempfile
OUT=Path(tempfile.gettempdir())/'fouritems_tensor_runs'/datetime.datetime.now().strftime('%Y%m%d_%H%M%S_%f')
OUT.mkdir(parents=True);shutil.copy2(__file__,OUT/'bianchi_tensor.py')
t,x,y,z=s.symbols('t x y z',real=True);coords=[t,x,y,z]
a=s.Function('a')(t);b=s.Function('b')(t)
g=s.diag(-1,a*a,b*b,b*b);gi=g.inv()
G=[[[s.simplify(sum(gi[k,l]*(s.diff(g[l,j],coords[i])+s.diff(g[l,i],coords[j])-s.diff(g[i,j],coords[l])) for l in range(4))/2)
     for j in range(4)] for i in range(4)] for k in range(4)]
ric=s.zeros(4)
for i in range(4):
    for j in range(4):
        ric[i,j]=s.simplify(sum(s.diff(G[k][i][j],coords[k])-s.diff(G[k][i][k],coords[j])+
             sum(G[k][i][j]*G[l][k][l]-G[l][i][k]*G[k][j][l] for l in range(4)) for k in range(4)))
scalar=s.simplify(sum(gi[i,j]*ric[i,j] for i in range(4) for j in range(4)))
ein=ric-g*scalar/2
Hx=s.diff(a,t)/a; Hy=s.diff(b,t)/b
expected=s.diag(2*Hx*Hy+Hy**2,
  a*a*(-2*s.diff(Hy,t)-3*Hy**2),
  b*b*(-s.diff(Hx,t)-s.diff(Hy,t)-Hx**2-Hy**2-Hx*Hy),
  b*b*(-s.diff(Hx,t)-s.diff(Hy,t)-Hx**2-Hy**2-Hx*Hy))
res=[s.simplify(ein[i,j]-expected[i,j]) for i in range(4) for j in range(4)]
assert all(r==0 for r in res)
xx,yy,bb,CC,V,P=s.symbols('Hx Hy baryons C V P',real=True)
theta=xx+2*yy
dx=(bb+CC+2*V+P)/2-theta*xx
dy=(bb+CC+2*V-P)/2-theta*yy
constraint=2*xx*yy+yy*yy-bb-CC-V
relations=[s.expand(-2*dy-3*yy**2-(P-V)-constraint),
           s.expand(-dx-dy-xx**2-yy**2-xx*yy-(-V)-constraint)]
assert all(r==0 for r in relations)
(OUT/'verification.json').write_text(json.dumps({'passed':True,'checks':18,
  'metric':'diag(-1,a(t)^2,b(t)^2,b(t)^2)','tensor_component_residuals':list(map(str,res)),
  'reduced_spatial_equation_residuals_mod_constraint':list(map(str,relations)),
  'scope':'symbolic tensor reduction, separate from Lean and numerical ODE existence'},indent=2),encoding='utf-8')
print(OUT)
