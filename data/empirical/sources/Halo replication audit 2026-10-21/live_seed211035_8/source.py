"""Symmetric live stock, exact inversion pairs, responding rigid disk.

Only one representative of each inversion pair is integrated. Its deposited
mass is both partners' mass; self subtraction removes ONE partner's own mass.
This equals the full paired calculation, not an extra smoothing prescription.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['NUMBA_NUM_THREADS']='1'
from fast_smooth_field import *
import argparse,json,time
from numba import set_num_threads
from live_bridge_fast import rigid_advance
from precessing_equilibrium import radial_tables,stock_target,target,diagnostic,NR,NF,NC,RB,MD,AD,TU
from precessing_equilibrium import potential as reference_potential
from fast_external import accel
HERE=Path(__file__).resolve().parent
set_num_threads(1)

@njit(cache=True)
def jacobi(X,V,om,lr,tab):
    out=np.zeros(len(X));ct=np.cos(43*np.pi/180);st=np.sin(43*np.pi/180)
    for i in range(len(X)):
        x,y,z=X[i];vx,vy,vz=V[i]
        out[i]=.5*(vx*vx+vy*vy+vz*vz)+reference_potential(x,y,z,.3,ct,st,lr,tab)-om*(y*vz-z*vy)
    return out

@njit(cache=True)
def baryon(X,mass,n):
    phi=np.zeros(len(X));tau=np.zeros(3);nx,ny,nz=n;MB=9e9;AB=.5;BD=.28
    for i in range(len(X)):
        x,y,z=X[i];r=np.sqrt(x*x+y*y+z*z);zz=x*nx+y*ny+z*nz;s=np.sqrt(zz*zz+BD*BD);den=np.sqrt(r*r-zz*zz+(AD+s)**2)
        phi[i]=-G*MD/den-G*MB/(r+AB);q=-G*MD/den**3*AD/s*zz*mass[i]
        tau[0]+=q*(y*nz-z*ny);tau[1]+=q*(z*nx-x*nz);tau[2]+=q*(x*ny-y*nx)
    return phi,tau

@njit(cache=True)
def split(X,V,mass,dt,n):
    delta=np.zeros(3);nx,ny,nz=n
    for i in range(len(X)):
        x,y,z=X[i];vx,vy,vz=V[i];lx=y*vz-z*vy;ly=z*vx-x*vz;lz=x*vy-y*vx;t=0.
        ax,ay,az=accel(x,y,z,nx,ny,nz)
        while t<dt-1e-15:
            r=np.sqrt(x*x+y*y+z*z);speed=np.sqrt(vx*vx+vy*vy+vz*vz);ac=np.sqrt(ax*ax+ay*ay+az*az)
            h=min(dt-t,.025*r/max(speed,1.),.025*np.sqrt(r/max(ac,1.)))
            vx+=.5*h*ax;vy+=.5*h*ay;vz+=.5*h*az;x+=h*vx;y+=h*vy;z+=h*vz
            ax,ay,az=accel(x,y,z,nx,ny,nz);vx+=.5*h*ax;vy+=.5*h*ay;vz+=.5*h*az;t+=h
        X[i,0]=x;X[i,1]=y;X[i,2]=z;V[i,0]=vx;V[i,1]=vy;V[i,2]=vz
        delta[0]+=mass[i]*(y*vz-z*vy-lx);delta[1]+=mass[i]*(z*vx-x*vz-ly);delta[2]+=mass[i]*(x*vy-y*vx-lz)
    return delta

@njit(cache=True)
def features(X,V,w,B):
    out=np.zeros(NR*NF)
    for i in range(len(X)):
        x,y,z=B@X[i];vx,vy,vz=B@V[i];r=np.sqrt(x*x+y*y+z*z)+1e-30;b=np.searchsorted(RB,r)-1
        if b<0 or b>=NR:continue
        ph=np.arctan2(z,x)%(2*np.pi);yy=y
        if ph>=np.pi:ph-=np.pi;yy=-y
        j=min(7,int(ph/np.pi*8));k=max(0,min(7,int((yy/r+1)*4)));out[b*NF+8*j+k]+=w[i]
        vr=(x*vx+y*vy+z*vz)/r;v2=vx*vx+vy*vy+vz*vz
        out[b*NF+NC]+=w[i]*vr*vr/40000;out[b*NF+NC+1]+=w[i]*(v2-vr*vr)/40000
        vals=np.array([x*x,y*y,z*z,x*y,x*z,y*z])
        for c in range(6):out[b*NF+NC+2+c]+=w[i]*vals[c]
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('--time',type=float,default=1.)
    ap.add_argument('--dt',type=float,default=.00025);ap.add_argument('--eps',type=float,default=.2)
    ap.add_argument('--rigid',action='store_true');ap.add_argument('--prior',action='store_true');ap.add_argument('--resume')
    ap.add_argument('--seed',default='quiet_seed.npz')
    args=ap.parse_args();out=HERE/args.tag;out.mkdir(exist_ok=False);(out/'source.py').write_bytes(Path(__file__).read_bytes());start=time.time()
    sd=np.load(HERE/args.seed);td=np.load(BRIDGE/'stars_seed_8192.npz');nn=len(sd['X'])//2;nt=len(td['X'])//2
    X=sd['X'][:nn].copy();V=sd['V'][:nn].copy();w=2*sd['prior' if args.prior else 'weights'][:nn];grid=sd['grid'];om=float(sd['Omega']);eps=args.eps
    Xs=td['X'][:nt].copy();Vs=td['V'][:nt].copy();ws=np.ones(nt)/nt
    tar,ms=stock_target();stars=target();mass=ms*w;zeros=np.zeros(nt);lr,tab,*_=radial_tables()
    Ld=MD*2*AD*220;L=np.array([0.,0.,Ld]);J0=L+np.sum(mass[:,None]*np.cross(X,V),axis=0);axis=J0/np.linalg.norm(J0)
    nodes=deposit(X,mass,grid,eps);acc,phi=evaluate(X,nodes,grid,eps,mass/2);as_,_=evaluate(Xs,nodes,grid,eps,zeros)
    phib,tau=baryon(X,mass,L/Ld);E0=mass@(.5*np.sum(V*V,axis=1)+.5*phi+phib);t0=0.
    if args.resume:
        prev=HERE/args.resume;old=json.loads((prev/'results.json').read_text());t0=old['rows'][-1]['time'];ss=np.load(prev/f'state_{t0:04.1f}.npz')
        X=ss['X'];V=ss['V'];Xs=ss['Xs'];Vs=ss['Vs'];L=ss['L'];E0=old['E0'];J0=np.array(old['J0']);axis=J0/np.linalg.norm(J0)
        nodes=deposit(X,mass,grid,eps);acc,phi=evaluate(X,nodes,grid,eps,mass/2);as_,_=evaluate(Xs,nodes,grid,eps,zeros);phib,tau=baryon(X,mass,L/np.linalg.norm(L))
    hj0=jacobi(X,V,om,lr,tab) if args.rigid else np.zeros(1);hjmax=0.
    rows=[];averages=[];ah=np.zeros(NR*NF);ast=ah.copy();nav=0;energymax=0.;jmax=0.;count=round((args.time-t0)/args.dt);dt=args.dt/TU
    for step in range(count+1):
        if step%max(1,round(.025/args.dt))==0:
            if not np.all(np.isfinite(Xs)) or not np.all(np.isfinite(phi)):
                raise RuntimeError('Nonfinite force or state, possibly outside the spline domain.')
            n=L/np.linalg.norm(L);xx=axis-(axis@n)*n;xx/=np.linalg.norm(xx);B=np.array([xx,np.cross(n,xx),n])
            if args.rigid:B=np.eye(3)
            h=features(X,V,w,B);s=features(Xs,Vs,ws,B);rr=np.linalg.norm(X,axis=1);J=L+np.sum(mass[:,None]*np.cross(X,V),axis=0)
            energy=float((mass@(.5*np.sum(V*V,axis=1)+.5*phi+phib)-E0)/abs(E0)) if not args.rigid else None
            if args.rigid:hjmax=max(hjmax,float(np.max(abs(jacobi(X,V,om,lr,tab)-hj0)/np.maximum(abs(hj0),1000))))
            je=float(np.linalg.norm(J-J0)/Ld);energymax=max(energymax,abs(energy or 0));jmax=max(jmax,je)
            row={'time':t0+step*args.dt,'stock':diagnostic(h,tar),'stars':diagnostic(s,stars),'energy_error':energy,'J_error_over_Ldisk':je,
                'disk_normal':n.tolist(),'disk_spin_fraction':float(np.linalg.norm(L)/Ld),'J_over_Ldisk':(J/Ld).tolist(),
                'mass_inside':{str(r):float(np.sum(mass[rr<r])) for r in [10,20,40,60,100]},'radii_extrema':[float(rr.min()),float(rr.max())],
                'maximum_speed':float(np.linalg.norm(V,axis=1).max()),'torque_over_required':(tau/(om*Ld)).tolist()}
            ah+=h;ast+=s;nav+=1
            if step%max(1,round(.5/args.dt))==0 or step==count:
                rows.append(row)
                if step:averages.append({'end':row['time'],'samples':nav,'stock':diagnostic(ah/nav,tar),'stars':diagnostic(ast/nav,stars)})
                ah[:]=0;ast[:]=0;nav=0
                result={'settings':vars(args),'E0':E0,'J0':J0.tolist(),'particles_represented':2*nn,'representatives_integrated':nn,'stock_mass':ms,'a0_SI':1.230729e-10,
                    'maximum_sampled_energy_error':energymax,'maximum_sampled_J_error':jmax,'maximum_sampled_Jacobi_error':hjmax if args.rigid else None,'rows':rows,'half_Gyr_averages':averages,'seconds':time.time()-start}
                (out/'results.json').write_text(json.dumps(result,indent=2));np.savez_compressed(out/f'state_{row["time"]:04.1f}.npz',X=X,V=V,Xs=Xs,Vs=Vs,L=L)
                print(json.dumps({'tag':args.tag,'t':row['time'],'stock_tilt':row['stock']['radial'][4]['tilt'],'stars':row['stars']['radial'][4]['tilt'],
                    'beta':row['stars']['radial'][1]['beta'],'Emax':energymax,'Jmax':jmax,'vmax':row['maximum_speed'],'seconds':time.time()-start}),flush=True)
        if step==count:break
        if args.rigid:
            rigid_advance(X,V,dt,om,lr,tab);rigid_advance(Xs,Vs,dt,om,lr,tab)
            if (step+1)%max(1,round(.025/args.dt))==0:phib,tau=baryon(X,mass,np.array([0.,0.,1.]))
        else:
            V+=.5*dt*acc;Vs+=.5*dt*as_;mid=L-.5*dt*tau;mid/=np.linalg.norm(mid)
            L-=split(X,V,mass,dt,mid);split(Xs,Vs,zeros,dt,mid)
            nodes=deposit(X,mass,grid,eps);acc,phi=evaluate(X,nodes,grid,eps,mass/2);as_,_=evaluate(Xs,nodes,grid,eps,zeros)
            V+=.5*dt*acc;Vs+=.5*dt*as_;phib,tau=baryon(X,mass,L/np.linalg.norm(L))
    print('Completed',args.tag,flush=True)

if __name__=='__main__':main()
