import json,numpy as np,sys; sys.path.insert(0,'/home/claude/lens'); import fwd as F
exec(open('/home/claude/lens/envfit.py').read().split("sets=")[0].replace("d=json.load","d=json.load"))
SO,SS,DM=[float(x) for x in sys.argv[2:5]] if len(sys.argv)>4 else (0.15,0.15,0.0)
f=lambda tc: F.obs_mean_mgal(0,sig_obs=SO,tc=tc,dlogm=DM)-F.MGAL_B21[0]
from scipy.optimize import brentq; TC=brentq(f,8.6,10.6)
Wp=[F.population(b,sig_obs=SO,sig_shmr=SS,tc=TC,dlogm=DM) for b in range(4)]
Ws=sum(Wp); ki=np.where(Ws.sum(1)>1e-7)[0]; kj=np.where(Ws.sum(0)>1e-7)[0]; LMG=F.mgal(F.LMS)
B0=np.exp(-F.ETA)*(1-F.FB)*F.MSP
temps=T_lin_bin+T_out_bin
print('budget multiplier k on M_sp budget: chi2 (no env | lin+out per bin)  inner(32)')
inner=np.tile(F.RAD<0.31,4)
for k in [float(x) for x in (sys.argv[5].split(",") if len(sys.argv)>5 else ["1","1.5","2","3","4","6","10","1e4"])]:
    pred=np.zeros(60)
    for b in range(4):
        acc=np.zeros(F.NR)
        for i in ki:
            for j in kj:
                if Wp[b][i,j]<1e-9: continue
                acc+=Wp[b][i,j]*F.esd_rar(LMG[i],k*B0[j])
        pred[b*F.NR:(b+1)*F.NR]=acc
    c0,_=fit(pred,[]); c1,x=fit(pred,temps)
    r=F.DATA-pred; Ci=F.COV[np.ix_(inner,inner)]
    print(f'k={k:7g}  {c0:7.1f} | {c1:7.1f}   inner {float(r[inner]@np.linalg.solve(Ci,r[inner])):6.1f}', flush=True)
