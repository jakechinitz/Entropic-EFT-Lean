# Mirror of Entropic/ReggeGraviton/Data.lean; emits literal moment values and Lean check files.
import pickle, itertools
from fractions import Fraction as F
permList=[list(p) for p in itertools.permutations(range(4))]
unit=[(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]
add=lambda x,y: tuple(a+b for a,b in zip(x,y)); sub=lambda x,y: tuple(a-b for a,b in zip(x,y)); sc=lambda c,x: tuple(c*a for a in x)
def vert(p,m):
    v=(0,0,0,0)
    for i in permList[p][:m]: v=add(v,unit[i])
    return v
edgeEnds=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
hz=[[0,0,0,0,0,3,0,-6,0,0],[0,-3,3,0,6,-6,0,3,0,0],[0,3,-2,0,-6,3,0,0,0,0],[0,0,0,0,0,0,0,0,0,0],[0,6,-6,0,-6,6,0,0,3,-6],
    [3,-6,3,0,6,-6,3,6,-6,3],[0,0,0,0,0,3,-2,-6,3,0],[-6,3,0,0,0,6,-6,-6,6,0],[0,0,0,0,3,-6,3,6,-3,0],[0,0,0,0,-6,3,0,0,0,0]]
typ=lambda p,e: sub(vert(p,edgeEnds[e][1]),vert(p,edgeEnds[e][0])); base=lambda p,e: vert(p,edgeEnds[e][0])
symIdx=[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]
def ec(v,c):
    if sum(v)>3: return 0
    m,n=symIdx[c]; return v[m]*v[n]*(1 if m==n else 2)
body=[(0,1,1,1),(1,0,1,1),(1,1,0,1),(1,1,1,0)]
dA=lambda p,e,f: add(add(sc(-1,typ(p,e)),sc(2,sub(base(p,f),base(p,e)))),typ(p,f))
dB=lambda p,e,f: add(sc(-1,typ(p,e)),sc(2,sub(base(p,f),base(p,e))))
def cA(c,d,p,e,f): return hz[e][f]*ec(typ(p,e),c)*ec(typ(p,f),d)
def cB(c,j,p,e,f): return hz[e][f]*ec(typ(p,e),c) if typ(p,f)==body[j] else 0
P=[(p,e,f) for p in range(24) for e in range(10) for f in range(10)]
up=[(i,l) for i in range(4) for l in range(i,4)]
mA={}
for c in range(10):
    for d in range(c,10):
        t=[(cA(c,d,*x),dA(*x)) for x in P]
        mA[(c,d)]=(sum(a for a,_ in t),[sum(a*D[i] for a,D in t) for i in range(4)],{(i,l):sum(a*D[i]*D[l] for a,D in t) for (i,l) in up})
mB={}
for c in range(10):
    for j in range(4):
        t=[(cB(c,j,*x),dB(*x)) for x in P]
        mB[(c,j)]=(sum(a for a,_ in t),[sum(a*D[i] for a,D in t) for i in range(4)])
assert all(v[0]==0 and v[1]==[0]*4 for v in mA.values()); assert all(v[0]==0 for v in mB.values())
# continuum target T(c,d)(i,l) symmetric, from (sqrt g R)^(2)
def T(c,d):
    def H(cc):
        m,n=symIdx[cc]; A=[[0]*4 for _ in range(4)]; A[m][n]=1; A[n][m]=1; return A
    A=H(c);B=H(d); trA=sum(A[i][i] for i in range(4)); trB=sum(B[i][i] for i in range(4)); AB=sum(A[i][j]*B[i][j] for i in range(4) for j in range(4))
    R=[[F(0)]*4 for _ in range(4)]
    for mu in range(4):
        for nu in range(4):
            v=F(0)
            if mu==nu: v+=F(-1,4)*AB+F(1,4)*trA*trB
            v+=F(1,2)*sum(A[mu][l]*B[nu][l] for l in range(4)); v+=F(-1,4)*(A[mu][nu]*trB+B[mu][nu]*trA); R[mu][nu]=v
    return [[(R[i][j]+R[j][i])/2 for j in range(4)] for i in range(4)]
# check: limit = -(1/384) k m2A k + (1/4608) sum_j (k.u_cj)(k.u_dj) == k T k
ok=True
for (c,d),(z0,z1,m2) in mA.items():
    Tm=T(c,d)
    for i in range(4):
        for l in range(4):
            a=m2[(min(i,l),max(i,l))]
            lhs=F(-1,384)*a + F(1,4608)*sum(F(mB[(c,j)][1][i]*mB[(d,j)][1][l]+mB[(c,j)][1][l]*mB[(d,j)][1][i],2) for j in range(4))
            if lhs!=Tm[i][l]: ok=False
print("limit identity:",ok)
pickle.dump((mA,mB),open("./moments.pkl","wb"))
print(mA[(0,0)], mB[(0,1)])
