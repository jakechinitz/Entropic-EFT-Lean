# Exact flat-space Hessian of the Regge action for one Kuhn 4-simplex, in squared-length variables.
import sympy as sp, itertools, pickle
V = 5
pairs = [(i,j) for i in range(V) for j in range(i+1,V)]          # 10 edges
s = {p: sp.Symbol(f"s{p[0]}{p[1]}", positive=True) for p in pairs}
def S(i,j): return 0 if i==j else s[(min(i,j),max(i,j))]
G = sp.Matrix(4,4, lambda a,b: (S(0,a+1)+S(0,b+1)-S(a+1,b+1))/2)
W = G.inv()   # dual metric, inward facet normals n_a (a=1..4), n_0 = -sum
def dot(a,b):
    if a>0 and b>0: return W[a-1,b-1]
    if a==0 and b==0: return sum(W[i,j] for i in range(4) for j in range(4))
    c = b if a==0 else a
    return -sum(W[i,c-1] for i in range(4))
tris = list(itertools.combinations(range(V),3))
def area(t):
    a,b,c = S(t[0],t[1]),S(t[1],t[2]),S(t[0],t[2])
    return sp.sqrt(2*a*b+2*b*c+2*c*a-a*a-b*b-c*c)/4
def theta(t):
    a,b = [v for v in range(V) if v not in t]
    return sp.acos(-dot(a,b)/sp.sqrt(dot(a,a)*dot(b,b)))
# Kuhn simplex: vertices 0,e1,e1+e2,.. -> squared length between chain vertices i<j is j-i
flat = {s[p]: p[1]-p[0] for p in pairs}
var = [s[p] for p in pairs]
h = sp.zeros(10,10)
for t in tris:
    gA = [sp.nsimplify(sp.simplify(sp.diff(area(t),x).subs(flat))) for x in var]
    gT = [sp.simplify(sp.diff(theta(t),x).subs(flat)) for x in var]
    for i in range(10):
        for j in range(10):
            h[i,j] += -gA[i]*gT[j]
h = h.applyfunc(sp.nsimplify)
h = h.applyfunc(sp.simplify)
print("symmetric:", sp.simplify(h-h.T)==sp.zeros(10,10))
# check flat dihedral angles and that sum over the 24 simplices around a triangle closes later
for t in tris: print(t, sp.nsimplify(theta(t).subs(flat)), area(t).subs(flat))
pickle.dump((pairs,h),open("./h_simplex.pkl","wb"))
print(h)
