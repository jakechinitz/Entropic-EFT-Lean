"""Data-conditioned cluster evolution with the unchanged archived Bose contact kernel."""
from pathlib import Path
import sys,json,time,math,argparse,shutil
from datetime import datetime
import numpy as np
from scipy.spatial import cKDTree

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source_snapshot'))
import descent3 as D
from descent_sim import build_fields
G,A0,C=D.G,D.A0,D.C

def init(name,N,seed):
    a=np.load(HERE/'inputs'/f'{name}.npz')
    meta=json.loads((HERE/'inputs/summary.json').read_text())[name]
    rng=np.random.default_rng(seed)
    # Stratified mass sampling reduces initial radial count noise without fitting a final state.
    q=(np.arange(N)+rng.random(N))/N; rng.shuffle(q)
    rr=np.interp(q,a['stock']/a['stock'][-1],a['r'])
    vr=np.zeros(N); ll=np.zeros(N)
    for i,ri in enumerate(rr):
        ps=np.interp(ri,a['r'],a['psi'])
        v=np.linspace(0,math.sqrt(2*ps),400)
        pdf=v*v*np.interp(ps-v*v/2,a['eg'],a['f'],left=0)
        cp=np.r_[0,np.cumsum(.5*(pdf[1:]+pdf[:-1])*np.diff(v))]
        assert cp[-1]>0
        speed=np.interp(rng.random()*cp[-1],cp,v)
        mu=rng.uniform(-1,1)
        vr[i]=speed*mu; ll[i]=ri*speed*math.sqrt(1-mu*mu)
    x,v=D.to3d(rr,vr,ll,rng)
    rg=np.geomspace(.5,30*meta['R200_model_kpc'],2200)
    # Exact same completed baryon mass used in Eddington inversion.
    from prepare import complete_mass
    bf,_=complete_mass(a['observed_r'],a['observed_b'])
    return x,v,rg,bf(rg),meta

def run(name,k=1,N=2000,T=10,seed=1,dt=.5,regspec=15000,sigc=0,label='primary',force='archived'):
    stamp=datetime.now().strftime('%Y%m%d_%H%M%S_%f')
    out=HERE/'runs'/f'{stamp}_{name}_k{k:g}_N{N}_s{seed}_{label}'
    out.mkdir(parents=True); shutil.copy2(__file__,out/'executed.py')
    pars=dict(cluster=name,k=k,N=N,T=T,seed=seed,dt_Myr=dt,contact_interval_Myr=2,initial_register_specific_km2_s2=regspec,gate_sigma_kms=sigc,label=label,force=force)
    (out/'parameters.json').write_text(json.dumps(pars,indent=2))
    x,v,rg,mb,meta=init(name,N,seed); M=meta['total_stock_Msun'];m=M/N
    if force=='conservative':
        import conservative_gravity as CG
        phi_baryon=CG.baryon_potential(rg,mb)
        shutil.copy2(HERE/'conservative_gravity.py',out/'conservative_gravity.py')
        energy_func=lambda:CG.energy(x,v,m,rg,phi_baryon)
        kick_func=lambda h:CG.kick(x,v,rg,phi_baryon,m,h)
    else:
        energy_func=lambda:D.stock_energy(x,v,m,rg,mb)
        kick_func=lambda h:D.kick(x,v,rg,g,h)
    r5=meta['R500_kpc'];r2=meta['R200_model_kpc'];vscale2=G*(meta['observed_total_M500'])/r5
    ncont=round(2/dt); assert abs(ncont*dt-2)<1e-10
    nsteps=round(T*1000/dt);saveevery=round(250/dt)
    hist=[];profiles=[];rawprofiles=[];t0=time.time();rng=np.random.default_rng(seed+11)
    rlog=np.geomspace(.1*r5,2*r5,90)
    rlog=np.unique(np.r_[rlog,.1*r5,.3*r5,.5*r5,r5,r2])
    b_log=np.interp(rlog,rg,mb)
    register=regspec*M; spenttot=0.;accepted=0;proposed=0;dPmax=0.;dLmax=0.;minregister=register;gatedintervals=0
    def fields():
        rr=np.linalg.norm(x,axis=1)
        return rr,build_fields(rg,mb,np.sort(rr),m,G,A0)
    rr,(g,gb,gs,J,Phi,unused,Ms)=fields()
    E0=energy_func()
    def record(t):
        energy=energy_func()
        ins=rr<r2;vi=v[ins];sig=float(np.sqrt(np.mean(np.sum((vi-vi.mean(0))**2,axis=1))/3))
        masses=m*np.searchsorted(np.sort(rr),rlog,side='right')
        profiles.append(masses+b_log);rawprofiles.append(masses)
        c5=m*int(np.sum(rr<=r5));b5=float(np.interp(r5,rg,mb))
        row=dict(t_Gyr=t,stock_at_R500_Msun=c5,total_at_R500_Msun=c5+b5,
             total_at_R500_over_HSE=(c5+b5)/meta['observed_total_M500'],
             sigma_kms=sig,accepted=accepted,proposed=proposed,
             work_specific_km2_s2=spenttot/M,register_specific_km2_s2=register/M,
             energy_residual_over_MV2=(energy-E0-spenttot)/(M*vscale2),
             F_bose_R500=D.F_bose(rg,gb,gs,r5),F_bose_R200=D.F_bose(rg,gb,gs,r2),
             frac_outside_R200=float(np.mean(rr>r2)),frac_outside_grid=float(np.mean(rr>rg[-1])),
             minimum_particle_radius_kpc=float(rr.min()))
        hist.append(row)
        with (out/'history.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
        if t==0 or abs(t-round(t))<1e-8:
            print(name,'k',k,'t',round(t,2),'M500/HSE',round(row['total_at_R500_over_HSE'],4),'sigma',round(sig),'work',round(spenttot/M,1),'acc',accepted,'dE',f"{row['energy_residual_over_MV2']:.2e}",flush=True)
    record(0)
    for s in range(nsteps):
        kick_func(.5*dt);D.drift(x,v,dt)
        rr,(g,gb,gs,J,Phi,unused,Ms)=fields()
        kick_func(.5*dt)
        if k>0 and s%ncont==0:
            gate=True
            if sigc>0:
                vi=v[rr<r2];gate=np.sqrt(np.mean(np.sum((vi-vi.mean(0))**2,axis=1))/3)<=sigc
            if gate:
                Om=np.sqrt(np.interp(rr,rg,g)/rr)*C
                np_=rng.poisson(k*Om*(ncont*dt)/(2*np.pi)).astype(np.int64)
                proposed+=int(np_.sum())
                if np_.sum()>0:
                    tree=cKDTree(x);_,idx=tree.query(x,k=2);partner=idx[:,1].astype(np.int64)
                    psi=D.psi_bose(rg,gb,gs)
                    pb=v.sum(0);lb=np.cross(x,v).sum(0)
                    acc,spent=D.contacts(x,v,partner,np_,rg,Phi,g,psi,register,m,int(seed*7919+s)%2**31)
                    pa=v.sum(0);la=np.cross(x,v).sum(0)
                    dPmax=max(dPmax,float(np.max(abs(pa-pb)))/(N*np.sqrt(vscale2)))
                    dLmax=max(dLmax,float(np.max(abs(la-lb)))/(N*np.sqrt(vscale2)*r2))
                    register-=spent;spenttot+=spent;accepted+=acc;minregister=min(minregister,register)
                    if register< -1e-9*regspec*M:raise RuntimeError('Negative register')
            else:gatedintervals+=1
        if (s+1)%saveevery==0 or s==nsteps-1:record((s+1)*dt/1000)
    profiles=np.array(profiles); rawprofiles=np.array(rawprofiles)
    late=np.array([h['t_Gyr']>=max(T-2,0) for h in hist])
    summary=dict(**pars,output=str(out),runtime_s=time.time()-t0,contact_delta_P_max_over_MV=dPmax,contact_delta_L_max_over_MVR=dLmax,
        max_abs_mechanical_ledger_residual_over_MV2=max(abs(h['energy_residual_over_MV2']) for h in hist),minimum_register_specific=minregister/M,
        accepted_contacts=accepted,proposed_contacts=proposed,gate_closed_intervals=gatedintervals,
        final_register_specific=register/M,late_mean_total_R500_over_HSE=float(np.mean([h['total_at_R500_over_HSE'] for h in hist if h['t_Gyr']>=max(T-2,0)])),
        late_std_total_R500_over_HSE=float(np.std([h['total_at_R500_over_HSE'] for h in hist if h['t_Gyr']>=max(T-2,0)])),
        initial_sigma_kms=hist[0]['sigma_kms'],final_sigma_kms=hist[-1]['sigma_kms'],
        F_bose_R500_final_over_initial=hist[-1]['F_bose_R500']/hist[0]['F_bose_R500'])
    np.savez_compressed(out/'profiles_and_state.npz',r_kpc=rlog,baryon_mass=b_log,t_Gyr=[h['t_Gyr'] for h in hist],total_mass=profiles,stock_mass=rawprofiles,late_mean_total_mass=profiles[late].mean(0),x_final=x,v_final=v)
    (out/'summary.json').write_text(json.dumps(summary,indent=2,allow_nan=False))
    print('COMPLETED',out,flush=True)
    return summary

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('cluster');p.add_argument('--k',type=float,default=1);p.add_argument('--N',type=int,default=2000);p.add_argument('--T',type=float,default=10);p.add_argument('--seed',type=int,default=1);p.add_argument('--dt',type=float,default=.5);p.add_argument('--regspec',type=float,default=15000);p.add_argument('--sigc',type=float,default=0);p.add_argument('--label',default='primary')
    p.add_argument('--force',choices=['archived','conservative'],default='archived')
    a=vars(p.parse_args());a['name']=a.pop('cluster');run(**a)
