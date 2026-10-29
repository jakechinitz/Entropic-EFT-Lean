import pickle, itertools, numpy as np, sympy as sp
pairs,h = pickle.load(open("./h_simplex.pkl","rb"))
h = np.array(h.tolist(),dtype=float)
types = [v for v in itertools.product([0,1],repeat=4) if any(v)]   # 15 edge types
tidx = {v:i for i,v in enumerate(types)}
simp = []   # list of (edge list of (type index, base vector)) per simplex, ordered like pairs
for perm in itertools.permutations(range(4)):
    verts=[np.zeros(4,int)]
    for p in perm:
        w=verts[-1].copy(); w[p]+=1; verts.append(w)
    simp.append([(tidx[tuple(verts[j]-verts[i])], verts[i]) for (i,j) in pairs])
def M(k):
    k=np.asarray(k,float); Mk=np.zeros((15,15),complex)
    for edges in simp:
        ph=np.array([np.exp(1j*k@b) for (_,b) in edges])
        for a,(ta,_) in enumerate(edges):
            for b,(tb,_) in enumerate(edges):
                Mk[ta,tb]+=h[a,b]*np.conj(ph[a])*ph[b]
    return Mk
# metric embedding: ds_v = v^mu v^nu h_mu nu  (10 symmetric components)
sym=[(m,n) for m in range(4) for n in range(m,4)]
def E(k=None, mid=False):
    Em=np.zeros((15,10),complex)
    for i,v in enumerate(types):
        v=np.array(v); ph = np.exp(1j*np.asarray(k)@v/2) if mid else 1
        for c,(m,n) in enumerate(sym):
            Em[i,c]=(v[m]*v[n]*(1 if m==n else 2))*ph
    return Em
def Kcont(k):
    # Hermitian kernel of (sqrt g R)^(2): -1/4 d h d h + 1/2 (d.h)^2 - 1/2 d.h d tr h + 1/4 (d tr h)^2
    k=np.asarray(k,float); K=np.zeros((10,10),complex)
    basis=[]
    for (m,n) in sym:
        H=np.zeros((4,4)); H[m,n]=H[n,m]=1; basis.append(H)
    for a,A in enumerate(basis):
        for b,B in enumerate(basis):
            k2=k@k
            t1=-0.25*k2*np.sum(A*B)
            t2=0.5*(k@A)@(k@B)
            t3=-0.25*((k@A@k)*np.trace(B)+(k@B@k)*np.trace(A))
            t4=0.25*k2*np.trace(A)*np.trace(B)
            K[a,b]=t1+t2+t3+t4
    return K
M0=M(np.zeros(4))
print("M(0) eigenvalues:",np.round(np.linalg.eigvalsh(M0),6))
print("||M(0)E|| =",np.linalg.norm(M0@E(np.zeros(4))))
# gauge zero modes
k=np.array([0.3,-0.2,0.5,0.1])
G=np.zeros((15,4),complex)
for i,v in enumerate(types):
    v=np.array(v); G[i]=2*v*(np.exp(1j*k@v)-1)
print("||M(k)G|| =",np.linalg.norm(M(k)@G))

# Low-energy subspace: kernel of M(0) (11-dim). Integrate out the 4 massive modes by Schur complement.
w,U=np.linalg.eigh(M0.real)
Kr=U[:,np.abs(w)<1e-9]; Ms=U[:,np.abs(w)>1e-9]
E0=E(np.zeros(4)).real
# basis for kernel: metric image + extra direction orthogonal to it within kernel
Q,_=np.linalg.qr(E0)
extra=Kr-Q@(Q.T@Kr); u,sv,_=np.linalg.svd(extra); f0=u[:,0]
print("extra zero mode (by edge type):")
for v,c in zip(types,f0): print(v,round(float(c),4))
def Keff(k,Bl):
    Mk=M(k); A=Bl.conj().T@Mk@Bl; Bm=Bl.conj().T@Mk@Ms; C=Ms.conj().T@Mk@Ms
    return A-Bm@np.linalg.solve(C,Bm.conj().T)
Bl=np.column_stack([E0,f0])
for eps in [1e-1,1e-2,1e-3]:
    kk=eps*np.array([0.3,-0.2,0.5,0.1])/np.linalg.norm([0.3,-0.2,0.5,0.1])
    K=Keff(kk,Bl)
    print(eps, "extra-extra:",np.round(K[10,10]/eps**2,6)," |metric-extra|/eps^2:",np.round(np.linalg.norm(K[:10,10])/eps**2,6))

print("\n--- metric effective kernel after integrating out all 5 non-metric modes ---")
# complement of metric image: f0 + massive modes
Fc=np.column_stack([f0,Ms])
def Kmetric(k, mid=False):
    Mk=M(k); Em=E(k,mid) if mid else E0.astype(complex)
    A=Em.conj().T@Mk@Em; B=Em.conj().T@Mk@Fc; C=Fc.conj().T@Mk@Fc
    return A-B@np.linalg.solve(C,B.conj().T)
rng=np.random.default_rng(1)
for trial in range(4):
    d=rng.normal(size=4); d/=np.linalg.norm(d)
    for eps in [1e-2,1e-3]:
        kk=eps*d
        K=Kmetric(kk)/eps**2; Kc=Kcont(d)
        c=np.vdot(Kc.ravel(),K.ravel()).real/np.vdot(Kc.ravel(),Kc.ravel()).real
        print(trial,eps,"c=",round(c,6),"rel resid=",np.linalg.norm(K-c*Kc)/np.linalg.norm(K))

print("\n--- checks ---")
d=np.array([0.3,-0.2,0.5,0.1]); xi=np.array([0.7,0.1,-0.4,0.2])
Hg=np.outer(d,xi)+np.outer(xi,d); hv=np.array([Hg[m,n] for (m,n) in sym])
print("Kcont gauge:",np.linalg.norm(Kcont(d)@hv))
for trial in range(3):
    d=rng.normal(size=4); d/=np.linalg.norm(d)
    eps=1e-3; K=Kmetric(eps*d,mid=True)/eps**2; Kc=Kcont(d)
    c=np.vdot(Kc.ravel(),K.ravel()).real/np.vdot(Kc.ravel(),Kc.ravel()).real
    print("mid",trial,"c=",round(c,6),"rel resid=",np.linalg.norm(K-c*Kc)/np.linalg.norm(K))

print("\n--- sector ratios Q_latt/Q_cont ---")
def vec(H): return np.array([H[m,n] for (m,n) in sym])
def tt_basis(d):
    # symmetric, transverse to d, traceless (4D): 5-dim
    P=np.eye(4)-np.outer(d,d)
    B=[]
    for (m,n) in sym:
        H=np.zeros((4,4)); H[m,n]=H[n,m]=1
        H=P@H@P; H-=np.trace(H)/3*P; B.append(vec(H))
    B=np.array(B).T; u,s,_=np.linalg.svd(B); return u[:,:5]
for trial in range(5):
    d=rng.normal(size=4); d/=np.linalg.norm(d)
    eps=1e-3; K=Kmetric(eps*d,mid=True)/eps**2; Kc=Kcont(d)
    T=tt_basis(d)
    # generalized eigenvalues on TT space
    A=T.T@K@T; B=T.T@Kc@T
    ev=np.linalg.eigvals(np.linalg.solve(B,A))
    print(trial,np.round(d,3),"TT ratios:",np.round(np.sort(ev.real),5))

print("\n--- coordinate reduction (Dittrich et al.) ---")
hd=tidx[(1,1,1,1)]; body=[tidx[v] for v in types if sum(v)==3]; met=[tidx[v] for v in types if sum(v)<=2]
k=np.array([0.31,-0.27,0.5,0.12])
print("hyperdiagonal row norm:",np.linalg.norm(M(k)[hd]))
# metric parametrization on the 10 short edges: ds_v = v v h (exact inverse exists)
Emet=np.zeros((15,10))
for i,v in enumerate(types):
    if sum(v)<=2:
        v=np.array(v)
        for c,(m,n) in enumerate(sym): Emet[i,c]=v[m]*v[n]*(1 if m==n else 2)
def Kred(kk):
    Mk=M(kk)
    A=Emet.T@Mk@Emet; B=Emet.T@Mk[:,body]; C=Mk[np.ix_(body,body)]
    return A-B@np.linalg.solve(C,B.conj().T)
worst=0
for trial in range(200):
    d=rng.normal(size=4); d/=np.linalg.norm(d)
    eps=1e-3; K=Kred(eps*d)/eps**2; Kc=Kcont(d)
    worst=max(worst,np.linalg.norm(K-Kc)/np.linalg.norm(Kc))
print("max over 200 directions of |K_latt/eps^2 - K_cont|/|K_cont| at eps=1e-3:",worst)
for eps in [1e-1,3e-2,1e-2]:
    d=np.array([0.31,-0.27,0.5,0.12]); d/=np.linalg.norm(d)
    print(eps, np.linalg.norm(Kred(eps*d)/eps**2-Kcont(d))/np.linalg.norm(Kcont(d)))

def Kred_mid(kk):
    Mk=M(kk); Em=np.zeros((15,10),complex)
    for i,v in enumerate(types):
        if sum(v)<=2:
            vv=np.array(v)
            for c,(m,n) in enumerate(sym): Em[i,c]=vv[m]*vv[n]*(1 if m==n else 2)*np.exp(1j*kk@vv/2)
    A=Em.conj().T@Mk@Em; B=Em.conj().T@Mk[:,body]; C=Mk[np.ix_(body,body)]
    return A-B@np.linalg.solve(C,B.conj().T)
print("midpoint embedding:")
for eps in [1e-1,3e-2,1e-2,3e-3]:
    errs=[]
    for trial in range(50):
        d=rng.normal(size=4); d/=np.linalg.norm(d)
        errs.append(np.linalg.norm(Kred_mid(eps*d)/eps**2-Kcont(d))/np.linalg.norm(Kcont(d)))
    print(eps, max(errs))

print("\n--- body-diagonal block over the Brillouin zone ---")
mx=-1e9; mn=1e9
g=np.linspace(-np.pi,np.pi,13)
for a in g:
  for b in g:
    for c in g:
      for d in g:
        Mk=M(np.array([a,b,c,d])); ev=np.linalg.eigvalsh(Mk[np.ix_(body,body)])
        mx=max(mx,ev.max()); mn=min(mn,ev.min())
print("eigenvalues of C(q) range over grid:",mn,mx)
