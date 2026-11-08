import json,numpy as np,sys; sys.path.insert(0,'/home/claude/lens'); import fwd as F
from scipy.optimize import nnls
tag=sys.argv[1] if len(sys.argv)>1 else 'so0.15_ss0.15_dm0.0'
d=json.load(open(f'/home/claude/lens/out_{tag}.json')); P={k:np.array(v) for k,v in d['pred'].items()}
W=[F.population(b) for b in range(4)]  # only for outer-template weights (approx with default pop)
# templates
LIN=F.esd_lin()
OUT=np.zeros((4,F.NR))
for b in range(4):
    w=W[b].sum(0); js=np.where(w>1e-4*w.max())[0]
    OUT[b]=sum(w[j]*F.esd_outer(j) for j in js)/w[js].sum()
L=np.linalg.cholesky(F.ICOV)   # ICOV = L L^T ; chi2 = |L^T r|^2
def fit(pred, temps):
    A=np.column_stack(temps) if temps else np.zeros((60,0))
    y=L.T@(F.DATA-pred); M=L.T@A
    if A.shape[1]: x,_=nnls(M,y)
    else: x=np.zeros(0)
    r=F.DATA-pred-(A@x if A.shape[1] else 0); return float(r@F.ICOV@r), x
def mask(v,b): z=np.zeros(60); z[b*F.NR:(b+1)*F.NR]=v; return z
T_lin_common=[np.concatenate([d['b_eff'][b]*LIN for b in range(4)])]
T_lin_bin=[mask(d['b_eff'][b]*LIN,b) for b in range(4)]
T_out_common=[np.concatenate(OUT)]
T_out_bin=[mask(OUT[b],b) for b in range(4)]
sets={'none':[], 'lin(1)':T_lin_common, 'lin+out(2)':T_lin_common+T_out_common,
      'lin per bin(4)':T_lin_bin, 'lin+out per bin(8)':T_lin_bin+T_out_bin}
print(f'{"env templates":22s}'+''.join(f'{m:>11s}' for m in P))
for s,T in sets.items():
    row=[fit(P[m],T) for m in P]
    print(f'{s:22s}'+''.join(f'{c:11.1f}' for c,_ in row))
for m in P:
    c,x=fit(P[m],T_lin_bin+T_out_bin); print(m,'per-bin amplitudes lin',np.round(x[:4],2),'outer b_e',np.round(x[4:],1))
