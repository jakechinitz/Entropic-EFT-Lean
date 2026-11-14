"""Idealized self-gravitating 3D stock, stars and SPH gas encounter.
Selected reciprocal multicarrier contact; no observational fit.
"""
from pathlib import Path
import argparse,json,time,hashlib,sys
import numpy as np
from numba import njit
from scipy.spatial import cKDTree
from scipy.stats import qmc,beta
HERE=Path(__file__).resolve().parent
PRIOR=HERE.parent/'Effective dynamics and coupling 2026-10-23'
sys.path.insert(0,str(PRIOR))
from hermitian_contact import speed
K_STOCK=5.1760752079627395
GAMMA=5/3

@njit(cache=True)
def gravity(x,m,eps):
    n=len(m);a=np.zeros_like(x);phi=np.zeros(n)
    for i in range(n):
        for j in range(i):
            d=x[i]-x[j];r2=np.dot(d,d)+eps*eps;inv=1/np.sqrt(r2)
            f=d*(inv/r2)
            a[i]-=m[j]*f;a[j]+=m[i]*f
            phi[i]-=m[j]*inv;phi[j]-=m[i]*inv
    return a,phi

@njit(cache=True)
def kernel(r,h):
    q=r/h
    if q>=2:return 0.,0.
    if q<1:
        f=1-1.5*q*q+.75*q**3;df=-3*q+2.25*q*q
    else:
        f=.25*(2-q)**3;df=-.75*(2-q)**2
    return f/(np.pi*h**3),df/(np.pi*h**4)

@njit(cache=True)
def density(x,m,h):
    n=len(m);rho=m/(np.pi*h**3)
    for i in range(n):
        for j in range(i):
            w,_=kernel(np.sqrt(np.sum((x[i]-x[j])**2)),h)
            rho[i]+=m[j]*w;rho[j]+=m[i]*w
    return rho

@njit(cache=True)
def hydro(x,v,m,u,rho,h,alpha=1.,beta_v=2.):
    n=len(m);a=np.zeros_like(x);du=np.zeros(n)
    cs=np.sqrt(GAMMA*(GAMMA-1)*u);A=(GAMMA-1)*u/rho
    for i in range(n):
        for j in range(i):
            r=x[i]-x[j];r2=np.dot(r,r)
            if r2==0 or r2>=4*h*h:continue
            _,dw=kernel(np.sqrt(r2),h);grad=dw*r/np.sqrt(r2)
            dv=v[i]-v[j];vr=np.dot(dv,r);pi=0.
            if vr<0:
                mu=h*vr/(r2+.01*h*h)
                pi=(-alpha*.5*(cs[i]+cs[j])*mu+beta_v*mu*mu)/(.5*(rho[i]+rho[j]))
            force=(A[i]+A[j]+pi)*grad
            a[i]-=m[j]*force;a[j]+=m[i]*force
            vg=np.dot(dv,grad)
            du[i]+=m[j]*(A[i]+.5*pi)*vg
            du[j]+=m[i]*(A[j]+.5*pi)*vg
    return a,du

def directions(u,v):
    z=2*u-1;p=2*np.pi*v;s=np.sqrt(1-z*z)
    return np.column_stack([s*np.cos(p),s*np.sin(p),z])

def sphere(n,mass,scale,seed,gas=False):
    assert n%4==0
    z=qmc.Sobol(6,scramble=True,seed=seed).random_base2(int(np.ceil(np.log2(n/4))))[:n//4]
    fmax=6**3/(1+6**2)**1.5
    r=scale/np.sqrt((z[:,0]*fmax)**(-2/3)-1)
    x=r[:,None]*directions(z[:,1],z[:,2])
    q=np.sqrt(beta.ppf(z[:,3],1.5,4.5))
    v=q[:,None]*np.sqrt(2*mass/np.sqrt(r*r+scale*scale))[:,None]*directions(z[:,4],z[:,5])
    X=np.concatenate([x,-x,x,-x]);V=np.concatenate([v,v,-v,-v])
    # Gas uses a second antipodal orientation rather than duplicate positions.
    if gas:
        rot=x[:,[1,2,0]]*np.array([1,-1,-1]);X=np.concatenate([x,-x,rot,-rot]);V[:]=0
    u=mass/(4*np.sqrt(np.sum(X*X,axis=1)+scale*scale)) if gas else np.zeros(n)
    return X,V,u

def initial(mult=1,seed=39177,isolated=False,collisionless_gas=False):
    frac=np.array([K_STOCK/(1+K_STOCK),.02,1/(1+K_STOCK)-.02])
    rows=[];ratio=.3;sep=np.array([8.,.6,0.]);rel=np.array([.8,0,0.])
    for c,mass in enumerate([1.] if isolated else [1.,ratio]):
        scale=mass**(1/3)
        centre=np.zeros(3) if isolated else (-ratio/(1+ratio)*sep if c==0 else sep/(1+ratio))
        bulk=np.zeros(3) if isolated else (ratio/(1+ratio)*rel if c==0 else -rel/(1+ratio))
        for kind,num in enumerate([384,96,192]):
            n=num*mult;isgas=kind==2 and not collisionless_gas
            X,V,u=sphere(n,mass,scale,seed+137*c+11*kind,isgas)
            core=(np.sum(X*X,axis=1)<scale*scale)&(kind==1)
            rows.append((X+centre,V+bulk,np.full(n,mass*frac[kind]/n),u,np.full(n,kind),np.full(n,c),core))
    return tuple(np.concatenate([r[k] for r in rows]) for k in range(7))

def logh(e):return np.logaddexp(np.log(.7)-e/.25,np.log(.3)-e)

def contacts(x,v,m,kind,cohort,clock,bath,nu,dt,rng,hc,eunit,stats):
    si=np.flatnonzero(kind==0);bi=np.flatnonzero(kind!=0)
    hits=si[rng.random(len(si))<-np.expm1(-nu*dt)]
    if not len(hits):return
    tree=cKDTree(x[bi])
    for i in hits:
        stats['attempts']+=1
        local=np.array(tree.query_ball_point(x[i],2*hc),dtype=int)
        if not len(local):stats['no_partner']+=1;continue
        cand=bi[local];dr=x[i]-x[cand];r=np.linalg.norm(dr,axis=1)
        weights=np.array([kernel(rr,hc)[0] for rr in r])*m[cand]
        if weights.sum()<=0:continue
        j=int(rng.choice(cand,p=weights/weights.sum()))
        d=x[i]-x[j];r=np.linalg.norm(d)
        if r<1e-12:continue
        n=d/r;dv=v[i]-v[j];old=float(dv@n);tangent=max(0.,float(dv@dv-old*old))
        logits=np.log([.7,.3])+.5*np.log([.25,1.])-tangent/(2*eunit*np.array([.25,1.]))
        probs=np.exp(logits-np.max(logits));probs/=sum(probs)
        temp=.25 if rng.random()<probs[0] else 1.
        new=rng.normal()*np.sqrt(eunit*temp)
        mu=m[i]*m[j]/(m[i]+m[j]);de=.5*mu*(new*new-old*old)
        heat=mu*eunit*1e-6*(logh((new*new+tangent)/(2*eunit))-logh((old*old+tangent)/(2*eunit)))
        work=de+heat;proposed=clock[i]-work;floor=m[i]*eunit
        if proposed<floor:stats['unaffordable_work']+=1;continue
        if bath[i]+heat<0:stats['unaffordable_heat']+=1;continue
        gate=speed(clock[i]/floor)*speed(proposed/floor)
        if rng.random()>=gate:continue
        delta=(new-old)*n
        before=.5*m[i]*(v[i]@v[i])+.5*m[j]*(v[j]@v[j])
        v[i]+=m[j]/(m[i]+m[j])*delta;v[j]-=m[i]/(m[i]+m[j])*delta
        after=.5*m[i]*(v[i]@v[i])+.5*m[j]*(v[j]@v[j])
        stats['event_energy_error']=max(stats['event_energy_error'],abs(after-before-de))
        clock[i]=proposed;bath[i]+=heat;stats['accepted']+=1
        stats['cross_cohort']+=int(cohort[i]!=cohort[j]);stats['work']+=work;stats['heat']+=heat

def invariants(x,v,m,u,gas,phi,clock,bath):
    kinetic=.5*np.sum(m[:,None]*v*v);potential=.5*m@phi;thermal=m[gas]@u[gas]
    return dict(energy=float(kinetic+potential+thermal+sum(clock)+sum(bath)),
                kinetic=float(kinetic),potential=float(potential),thermal=float(thermal),
                clock=float(sum(clock)),bath=float(sum(bath)),
                momentum=np.sum(m[:,None]*v,axis=0).tolist(),
                angular=np.sum(m[:,None]*np.cross(x,v),axis=0).tolist())

def evolve(args):
    out=HERE/'results'/args.tag;out.mkdir(exist_ok=False)
    (out/'executed_source.py').write_bytes(Path(__file__).read_bytes())
    (out/'protocol.txt').write_bytes((HERE/'PROTOCOL.txt').read_bytes())
    (out/'settings.json').write_text(json.dumps(vars(args),indent=2))
    x,v,m,u,kind,cohort,core=initial(args.mult,args.seed,args.isolated,args.collisionless_gas)
    gas=np.flatnonzero((kind==2)&(not args.collisionless_gas));stock=kind==0
    rng=np.random.default_rng(args.seed+901);clock=np.zeros(len(m));bath=np.zeros(len(m))
    eunit=.2;clock[stock]=m[stock]*eunit*(1+args.available);bath[stock]=m[stock]*eunit*1e-4
    h=args.h;eps=args.eps;dt=args.dt;hc=args.contact_h
    ag,phi=gravity(x,m,eps)
    rho=density(x[gas],m[gas],h)
    base=invariants(x,v,m,u,gas,phi,clock,bath)
    stats={k:0 for k in ['attempts','no_partner','accepted','cross_cohort','unaffordable_work','unaffordable_heat']}
    stats.update(event_energy_error=0.,work=0.,heat=0.)
    np.savez_compressed(out/'initial.npz',x=x,v=v,m=m,u=u,kind=kind,cohort=cohort,core=core,clock=clock,bath=bath)
    hist=[];snap=[];start=time.time();steps=round(args.end/dt);stride=max(1,round(.2/dt))
    for k in range(steps+1):
        if k%stride==0 or k==steps:
            inv=invariants(x,v,m,u,gas,phi,clock,bath)
            centres=[];rhalf=[]
            for c in np.unique(cohort):
                ix=(cohort==c)&core;centre=np.average(x[ix],axis=0,weights=m[ix]);centres.append(centre.tolist())
                rhalf.append([float(np.median(np.linalg.norm(x[(cohort==c)&(kind==j)]-centre,axis=1))) for j in range(3)])
            row={'time':k*dt,**inv,'core_centres':centres,'median_radii_about_core':rhalf,
                 'min_gas_u':float(u[gas].min()) if len(gas) else None,
                 'min_clock_above_floor':float(np.min(clock[stock]/(m[stock]*eunit)-1)),
                 'min_bath':float(bath[stock].min()),'max_clock_speed':max(speed(e) for e in clock[stock]/(m[stock]*eunit)),
                 'accepted':stats['accepted'],'cross_cohort':stats['cross_cohort']}
            hist.append(row);snap.append((x.copy(),v.copy(),u.copy(),clock.copy(),bath.copy(),rho.copy()))
            if k%(stride*5)==0 or k==steps:
                print(json.dumps({'tag':args.tag,'t':k*dt,'energy_error':(inv['energy']-base['energy'])/abs(base['potential']),
                                  'events':stats['accepted'],'seconds':time.time()-start}),flush=True)
        if k==steps:break
        if len(gas):
            ah,du0=hydro(x[gas],v[gas],m[gas],u[gas],rho,h)
        else:ah=np.empty((0,3));du0=np.empty(0)
        a0=ag.copy();a0[gas]+=ah
        half=v+.5*dt*a0;x=x+dt*half
        ag,phi=gravity(x,m,eps);rho=density(x[gas],m[gas],h)
        vn=half+.5*dt*ag;un=u.copy();un[gas]+=dt*du0
        if np.any(un[gas]<=0):raise RuntimeError('Negative predictor gas energy; reduce timestep, do not clip')
        # Implicit velocity-dependent final kick; symmetric central forces.
        for iteration in range(8):
            ah,du1=hydro(x[gas],vn[gas],m[gas],un[gas],rho,h)
            anew=ag.copy();anew[gas]+=ah
            vnext=half+.5*dt*anew;unext=u.copy();unext[gas]+=.5*dt*(du0+du1)
            err=max(np.max(abs(vnext-vn)),np.max(abs(unext-un)))
            vn,un=vnext,unext
            if err<1e-11:break
        if np.any(un[gas]<=0) or not np.isfinite(vn).all():raise RuntimeError('Invalid gas energy/state; no clipping')
        v,u=vn,un
        if args.nu>0:contacts(x,v,m,kind,cohort,clock,bath,args.nu,dt,rng,hc,eunit,stats)
    p0=np.array(base['momentum']);l0=np.array(base['angular'])
    report={'settings':vars(args),'particles':len(m),'base':base,'history':hist,'contact':stats,
            'wall_seconds':time.time()-start,'stock_per_baryon':K_STOCK,
            'max_energy_error_over_initial_binding':max(abs(r['energy']-base['energy'])/abs(base['potential']) for r in hist),
            'max_momentum_error':max(np.linalg.norm(np.array(r['momentum'])-p0) for r in hist),
            'max_angular_error':max(np.linalg.norm(np.array(r['angular'])-l0) for r in hist),
            'minimum_clock_surplus':min(r['min_clock_above_floor'] for r in hist),
            'minimum_bath':min(r['min_bath'] for r in hist),
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'physical_rate_selected':False,'observational_fit':False,'clips':False}
    with (out/'result.json').open('x',encoding='utf-8') as f:json.dump(report,f,indent=2)
    np.savez_compressed(out/'history.npz',time=np.array([r['time'] for r in hist]),x=np.array([s[0] for s in snap]),
                        v=np.array([s[1] for s in snap]),u=np.array([s[2] for s in snap]),clock=np.array([s[3] for s in snap]),
                        bath=np.array([s[4] for s in snap]),rho_gas=np.array([s[5] for s in snap]),m=m,kind=kind,cohort=cohort,core=core)
    print(json.dumps({k:v for k,v in report.items() if k not in ['base','history']}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--tag',required=True);p.add_argument('--mult',type=int,default=1)
    p.add_argument('--seed',type=int,default=39177);p.add_argument('--dt',type=float,default=.01)
    p.add_argument('--end',type=float,default=12.);p.add_argument('--nu',type=float,default=0.)
    p.add_argument('--available',type=float,default=1.2);p.add_argument('--h',type=float,default=.45)
    p.add_argument('--eps',type=float,default=.1);p.add_argument('--contact-h',type=float,default=.45)
    p.add_argument('--isolated',action='store_true');p.add_argument('--collisionless-gas',action='store_true')
    evolve(p.parse_args())
