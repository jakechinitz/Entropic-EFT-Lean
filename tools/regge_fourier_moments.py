# Exact Fourier data of the reduced kernel K(q) = E^dag M E + 2 B B^dag (body block C = -1/2 I).
# Entries: K(q)_{cd} = sum_j c_j exp(i q.D_j/2), D_j in Z^4, c_j rational (x48 -> integer).
import pickle, itertools, sympy as sp
from collections import defaultdict
from fractions import Fraction as F
pairs,h = pickle.load(open("./h_simplex.pkl","rb"))
h=[[F(str(h[i,j])) for j in range(10)] for i in range(10)]
types=[v for v in itertools.product([0,1],repeat=4) if any(v)]; tidx={v:i for i,v in enumerate(types)}
simp=[]
for perm in itertools.permutations(range(4)):
    verts=[(0,0,0,0)]
    for p in perm:
        w=list(verts[-1]); w[p]+=1; verts.append(tuple(w))
    simp.append([(tidx[tuple(a-b for a,b in zip(verts[j],verts[i]))], verts[i]) for (i,j) in pairs])
add=lambda x,y: tuple(a+b for a,b in zip(x,y)); sub=lambda x,y: tuple(a-b for a,b in zip(x,y)); sc=lambda c,x: tuple(c*a for a in x)
# M as dict: M[a][b] = {D(doubled displacement): coeff}
M=[[defaultdict(F) for _ in range(15)] for _ in range(15)]
for edges in simp:
    for a,(ta,ba) in enumerate(edges):
        for b,(tb,bb) in enumerate(edges):
            if h[a][b]!=0: M[ta][tb][sc(2,sub(bb,ba))]+=h[a][b]
# C block check
body=[tidx[v] for v in types if sum(v)==3]
for a in body:
    for b in body:
        d={D:c for D,c in M[a][b].items() if c!=0}
        assert d==({(0,0,0,0):F(-1,2)} if a==b else {}), (a,b,d)
print("C(q) = -1/2 I exactly")
hd=tidx[(1,1,1,1)]
assert all(c==0 for b in range(15) for c in M[hd][b].values())
print("hyperdiagonal row identically zero")
sym=[(m,n) for m in range(4) for n in range(m,4)]
def Ecoef(v,c):
    m,n=sym[c]; return v[m]*v[n]*(1 if m==n else 2)
kept=[i for i,v in enumerate(types) if sum(v)<=3]
# E_{a c}(q) = Ecoef * exp(i q.v/2) -> doubled displacement v ; conj -> -v
def Kentry(c,d):
    out=defaultdict(F)
    # E^dag M E over all kept a,b (metric part incl. body at metric values)
    for a in kept:
        for b in kept:
            ea=Ecoef(types[a],c); eb=Ecoef(types[b],d)
            if ea==0 or eb==0: continue
            for D,x in M[a][b].items():
                out[add(add(sc(-1,types[a]),D),types[b])]+=ea*eb*x
    # + 2 B B^dag, B_{c,body} = sum_a conj(E_ac) M_{a,body}  (metric-to-fluctuation coupling)
    for j in body:
        Bc=defaultdict(F); Bd=defaultdict(F)
        for a in kept:
            ea=Ecoef(types[a],c); ed=Ecoef(types[a],d)
            for D,x in M[a][j].items():
                if ea: Bc[add(sc(-1,types[a]),D)]+=ea*x
                if ed: Bd[add(sc(-1,types[a]),D)]+=ed*x
        # B_c * conj(B_d): conj of term exp(i q.D/2) is exp(-i q.D/2)
        for D1,x1 in Bc.items():
            for D2,x2 in Bd.items():
                out[sub(D1,D2)]+=2*x1*x2
    return {D:x for D,x in out.items() if x!=0}
K={(c,d):Kentry(c,d) for c in range(10) for d in range(10)}
# moments: sum c =0, sum c D =0, -(1/8) sum c D D^T == K_EH second-order coefficient
import numpy as np
ok=True
for (c,d),terms in K.items():
    s0=sum(terms.values()); s1=[sum(x*D[i] for D,x in terms.items()) for i in range(4)]
    if s0!=0 or any(s1): ok=False
print("zeroth and first moments vanish:",ok)
# Hermiticity: K_dc(D) == conj K_cd -> coefficient of -D in K_cd
herm=all(K[(d,c)].get(D,0)==K[(c,d)].get(sc(-1,D),0) for c in range(10) for d in range(10) for D in set(K[(c,d)])|set(K[(d,c)]))
print("Hermitian:",herm)
print("max terms per entry:",max(len(t) for t in K.values()), " total terms:",sum(len(t) for t in K.values()))
den=1
import math
for t in K.values():
    for x in t.values(): den=math.lcm(den,x.denominator)
print("common denominator:",den)
pickle.dump((sym,K),open("./Kdata.pkl","wb"))

from fractions import Fraction as F
def KEH_coef(c,d):
    # second-order coefficient tensor T[mu][nu] with K_EH(k)_{cd} = sum T k_mu k_nu (symmetrized)
    def H(cc):
        m,n=sym[cc]; A=[[0]*4 for _ in range(4)]; A[m][n]=1; A[n][m]=1; return A
    A=H(c); B=H(d); T=[[F(0)]*4 for _ in range(4)]
    trA=sum(A[i][i] for i in range(4)); trB=sum(B[i][i] for i in range(4))
    AB=sum(A[i][j]*B[i][j] for i in range(4) for j in range(4))
    for mu in range(4):
        for nu in range(4):
            v=F(0)
            if mu==nu: v+=F(-1,4)*AB+F(1,4)*trA*trB
            v+=F(1,2)*sum(A[mu][l]*B[nu][l] for l in range(4))
            v+=F(-1,4)*(A[mu][nu]*trB+B[mu][nu]*trA)
            T[mu][nu]=v
    # symmetrize
    return [[(T[i][j]+T[j][i])/2 for j in range(4)] for i in range(4)]
ok2=True; ok3=True
for (c,d),terms in K.items():
    S2=[[F(-1,8)*sum(x*D[i]*D[j] for D,x in terms.items()) for j in range(4)] for i in range(4)]
    if S2!=KEH_coef(c,d): ok2=False
    for i in range(4):
        for j in range(4):
            for l in range(4):
                if sum(x*D[i]*D[j]*D[l] for D,x in terms.items())!=0: ok3=False
print("second moment == linearized Einstein-Hilbert:",ok2)
print("third moments vanish:",ok3)
