# Exact Taylor certificate: K_latt(eps*k) = eps^2 K_EH(k) + 0*eps^3 + O(eps^4), symbolic k, rational arithmetic.
import pickle, itertools, sympy as sp
pairs,h = pickle.load(open("./h_simplex.pkl","rb"))
types=[v for v in itertools.product([0,1],repeat=4) if any(v)]; tidx={v:i for i,v in enumerate(types)}
k=sp.symbols('k1:5'); e=sp.Symbol('e'); I=sp.I
def ph(vec,order=3):  # exp(i e k.vec) truncated
    x=I*e*sum(ki*vi for ki,vi in zip(k,vec)); return sum(x**n/sp.factorial(n) for n in range(order+1))
simp=[]
for perm in itertools.permutations(range(4)):
    verts=[(0,0,0,0)]
    for p in perm:
        w=list(verts[-1]); w[p]+=1; verts.append(tuple(w))
    simp.append([(tidx[tuple(a-b for a,b in zip(verts[j],verts[i]))], verts[i]) for (i,j) in pairs])
def trunc(x,n=3): return sp.series(sp.expand(x),e,0,n+1).removeO() if x!=0 else 0
# Build M(k) truncated to e^3 (phases combine: conj(ph_a) ph_b = exp(i e k.(b_b-b_a)))
M=sp.zeros(15,15)
for edges in simp:
    for a,(ta,ba) in enumerate(edges):
        for b,(tb,bb) in enumerate(edges):
            if h[a,b]!=0:
                M[ta,tb]+=h[a,b]*ph(tuple(y-x for x,y in zip(ba,bb)))
sym=[(m,n) for m in range(4) for n in range(m,4)]
met=[tidx[v] for v in types if sum(v)<=2]; body=[tidx[v] for v in types if sum(v)==3]
Em=sp.zeros(15,10)
for v in types:
    if sum(v)<=3:
        for c,(m,n) in enumerate(sym): Em[tidx[v],c]=v[m]*v[n]*(1 if m==n else 2)*ph(tuple(sp.Rational(x,2) for x in v))
Emc=Em.applyfunc(lambda z: z.subs(I,-I))  # conjugate (k,e real)
A=(Emc.T*M*Em).applyfunc(lambda z: trunc(z))
Bm=(Emc.T*M[:,body]).applyfunc(lambda z: trunc(z))
C=M.extract(body,body).applyfunc(lambda z: trunc(z))
C0=C.subs(e,0); C1=C.applyfunc(lambda z: sp.expand(z).coeff(e,1))
C0i=C0.inv()
B1=Bm.applyfunc(lambda z: sp.expand(z).coeff(e,1)); B2=Bm.applyfunc(lambda z: sp.expand(z).coeff(e,2))
B0=Bm.subs(e,0)
print("B0 == 0:", B0==sp.zeros(10,4), "  C0 =", C0.tolist())
Ai=[A.applyfunc(lambda z,i=i: sp.expand(z).coeff(e,i)) for i in range(4)]
B1c=B1.applyfunc(lambda z: z.subs(I,-I)); B2c=B2.applyfunc(lambda z: z.subs(I,-I))
# Schur series: B C^{-1} B^dagger with B^dagger = conj(B)^T ; C^{-1}=C0i - e C0i C1 C0i
S2=B1*C0i*B1c.T
S3=B2*C0i*B1c.T + B1*C0i*B2c.T - B1*C0i*C1*C0i*B1c.T
K0=Ai[0]; K1=Ai[1]; K2=(Ai[2]-S2).applyfunc(sp.expand); K3=(Ai[3]-S3).applyfunc(sp.expand)
# continuum kernel
def Kc():
    K=sp.zeros(10,10); basis=[]
    for (m,n) in sym:
        H=sp.zeros(4,4); H[m,n]=1; H[n,m]=1; basis.append(H)
    kv=sp.Matrix(k); k2=(kv.T*kv)[0]
    for a,Aa in enumerate(basis):
        for b,Bb in enumerate(basis):
            K[a,b]=(-sp.Rational(1,4)*k2*sum(Aa[i,j]*Bb[i,j] for i in range(4) for j in range(4))
                    +sp.Rational(1,2)*((kv.T*Aa)*(Bb*kv))[0]
                    -sp.Rational(1,4)*((kv.T*Aa*kv)[0]*Bb.trace()+(kv.T*Bb*kv)[0]*Aa.trace())
                    +sp.Rational(1,4)*k2*Aa.trace()*Bb.trace())
    return K
KC=Kc()
print("order e^0 zero:", K0.applyfunc(sp.expand)==sp.zeros(10,10))
print("order e^1 zero:", K1.applyfunc(sp.expand)==sp.zeros(10,10))
print("order e^2 == K_EH:", (K2-KC).applyfunc(sp.expand)==sp.zeros(10,10))
print("order e^3 zero:", K3==sp.zeros(10,10))
pickle.dump({"A":Ai,"B1":B1,"B2":B2,"C0":C0,"C1":C1,"KC":KC},open("./exact.pkl","wb"))
