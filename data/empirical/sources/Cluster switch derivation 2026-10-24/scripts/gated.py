"""Run GPT's evolve.run with the Bose free energy restricted to the record-dominated support r<r_d.
F = int_{r<r_d} N Theta D d^3x, so d psi/dr = 0 for r>r_d and psi(r_d)=0. Everything else unchanged."""
import sys,json,numpy as np
from pathlib import Path
HERE=Path(__file__).resolve().parent; sys.path.insert(0,str(HERE))
import evolve, descent3 as D
orig=D.psi_bose
def make(rd):
    def psi_gated(rg,gb,gs):
        xg=np.sqrt(gb/D.A0); ns=1/np.expm1(xg); n=np.maximum(gs/gb,1e-12)
        dpsi=gb*ns*(1+ns)*(np.log1p(1/n)-xg)
        dpsi=np.where(rg<=rd,dpsi,0.0)
        psi=np.zeros_like(rg)
        psi[:-1]=-np.cumsum((0.5*(dpsi[1:]+dpsi[:-1])*np.diff(rg))[::-1])[::-1]
        return psi
    return psi_gated
if __name__=='__main__':
    name=sys.argv[1]; k=float(sys.argv[2]); rd=float(sys.argv[3]); regspec=float(sys.argv[4]); T=float(sys.argv[5]); label=sys.argv[6]
    if rd>0: D.psi_bose=make(rd)
    evolve.run(name,k=k,N=2000,T=T,seed=1,dt=.1,regspec=regspec,label=label,force='conservative',softening=5.)
