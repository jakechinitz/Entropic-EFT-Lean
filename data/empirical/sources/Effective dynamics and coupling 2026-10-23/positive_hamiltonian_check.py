"""Positive completion of the joint Hamiltonian's exchange edges.
Energy conservation alone does not ensure that an arbitrary interaction
preserves the free lower bound. Each edge is completed to a positive
rank-one form, with the least equal diagonal shift for its off-diagonal.
"""
from pathlib import Path
import json,numpy as np
from scipy.linalg import eigh
from hermitian_contact import speed
HERE=Path(__file__).resolve().parent
out=HERE/'results/positive_hamiltonian.json';assert not out.exists()
states=[(i,u,b,m) for i in range(2) for u in range(1,7) for b in range(2) for m in range(3)]
index={s:k for k,s in enumerate(states)};dim=len(states)
energies=np.array([2*i+u+b for i,u,b,m in states],float)
H0=np.diag(energies);Hc=np.zeros((dim,dim),complex);g=.2
for u in range(4,7):
    for m in range(3):
        a=index[(0,u,0,m)];b=index[(1,u-3,1,m)]
        c=g*np.sqrt(speed(u)*speed(u-3))
        Hc[a,a]+=c;Hc[b,b]+=c;Hc[a,b]-=c;Hc[b,a]-=c
Jx=np.array([[0,1,0],[1,0,1],[0,1,0]],complex)/np.sqrt(2)
Jy=np.array([[0,1j,0],[-1j,0,1j],[0,-1j,0]],complex)/np.sqrt(2)
Jz=np.diag([-1.,0.,1.]);J=[np.kron(np.eye(dim//3),x) for x in [Jx,Jy,Jz]]
floor=np.diag([float(u==1) for i,u,b,m in states]);H=H0+Hc
val,vec=eigh(H);initial=np.zeros(dim,complex);initial[index[(0,5,0,1)]]=1
coef=vec.conj().T@initial;t=np.linspace(0,100,2001)
psi=vec@(coef[:,None]*np.exp(-1j*val[:,None]*t[None,:]));probs=abs(psi)**2
totalE=energies@probs;U=np.array([u for i,u,b,m in states])@probs
report={'scope':__doc__,'dimension':dim,
 'hermiticity_error':float(abs(Hc-Hc.conj().T).max()),
 'minimum_interaction_eigenvalue':float(np.linalg.eigvalsh(Hc).min()),
 'minimum_full_hamiltonian_eigenvalue':float(val.min()),'free_floor':1.,
 'bare_energy_commutator_max':float(abs(H0@Hc-Hc@H0).max()),
 'angular_commutators_max':[float(abs(A@Hc-Hc@A).max()) for A in J],
 'floor_coupling_max':float(abs(Hc@floor).max()),
 'max_norm_error':float(abs(probs.sum(0)-1).max()),
 'max_bare_energy_drift':float(abs(totalE-totalE[0]).max()),
 'min_mean_clock_energy':float(U.min()),
 'dissipative_relaxation_claimed':False,'actual_scalar_spectrum_identified':False,
 'weak_coupling_limitation':'The diagonal completion must be included when matching frequency shifts and finite-coupling rates.'}
out.write_text(json.dumps(report,indent=2),encoding='utf-8')
np.savez_compressed(HERE/'results/positive_hamiltonian_arrays.npz',H0=H0,Hc=Hc,t=t,clock_energy=U,total_energy=totalE)
print(json.dumps(report))
