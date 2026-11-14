"""Preserve source snapshots and construct data-conditioned cluster initial models."""
from pathlib import Path
import sys, json, hashlib, tarfile, shutil
import numpy as np
from scipy.optimize import least_squares, brentq
from scipy.interpolate import PchipInterpolator
from scipy.integrate import cumulative_trapezoid

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OLD=ROOT/'Observed cluster tests 2026-10-23'
CLAUDE=ROOT/'Contact rule physical basis 2026-10-24'
GAL=ROOT/'Galaxy sector resolution 2026-10-24'
SRC=HERE/'source_snapshot'
NAMES=['A85','A1795','A2029','A2142','A2319','A644','ZW1215']
G=4.30091e-6
A0=1.2307e-10*3.0857e19/1e6
NF=lambda x:np.log1p(x)-x/(1+x)

def snapshots():
    SRC.mkdir(exist_ok=True)
    originals=[CLAUDE/'descent3.py',CLAUDE/'Research note/findings.tex',CLAUDE/'summary_runs_bose.txt',CLAUDE/'runD.sh',GAL/'descent2.py',GAL/'static_analysis.py',GAL/'Repairs - 3D contacts and exact minimiser/minimizer.py',OLD/'radial_analysis.py',OLD/'source_data/lensing_table_A2.json']
    manifest=[]
    for p in originals:
        dest=SRC/p.name
        if dest.exists(): assert dest.read_bytes()==p.read_bytes()
        else: shutil.copy2(p,dest)
        manifest.append(dict(original=str(p),snapshot=str(dest),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
    with tarfile.open(GAL/'audit_trail_v1.tar.gz') as tf:
        members=[m for m in tf.getmembers() if m.name=='descent_sim.py']
        assert len(members)==1
        b=tf.extractfile(members[0]).read()
        dest=SRC/'descent_sim.py'
        if dest.exists():assert dest.read_bytes()==b
        else:dest.write_bytes(b)
        manifest.append(dict(original=str(GAL/'audit_trail_v1.tar.gz')+'::descent_sim.py',sha256=hashlib.sha256(b).hexdigest()))
    for name in NAMES:
        for suffix in ['hydro_mass','fgas_profile','mstar']:
            p=OLD/f'source_data/xcop/{name}/{name}_{suffix}.fits'
            manifest.append(dict(original=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
    (HERE/'source_manifest.json').write_text(json.dumps(manifest,indent=2))

def complete_mass(rr,mm):
    f=PchipInterpolator(np.log(rr),np.log(mm))
    lo,hi=rr[0],rr[-1]; blo,bhi=mm[0],mm[-1]
    slope=float(f.derivative()(np.log(hi)))
    assert slope>=0
    def mass(r):
        r=np.asarray(r,dtype=float)
        val=np.exp(f(np.log(np.clip(r,lo,hi))))
        val=np.where(r<lo,blo*(r/lo)**2,val)
        val=np.where(r>hi,bhi*(1+.5*slope*(1-(hi/np.maximum(r,hi))**2)),val)
        return val
    return mass,dict(inner_power=2,outer_log_slope_at_join=slope,outer_added_mass_over_join_mass=.5*slope)

def main():
    snapshots()
    sys.path.insert(0,str(OLD))
    import radial_analysis as obs
    inputs=HERE/'inputs'; inputs.mkdir(exist_ok=True)
    report={}; lens=json.loads((OLD/'source_data/lensing_table_A2.json').read_text())['clusters']
    for name in NAMES:
        hd,ma,ga,rg,st=obs.profile(name); r5=float(hd['R500']); z=float(hd['REDSHIFT'])
        lo=max(.1*r5,float(rg.min()),float(ma['RADIUS'].min()),float(st['RADIUS'].min()))
        hi=min(1.5*r5,float(rg.max()),float(ma['RADIUS'].max()),float(st['RADIUS'].max()))
        ro=np.geomspace(lo,hi,200)
        bo=obs.interp(rg,ga['MGAS'])(ro)+obs.stellar(st,ro,r5)
        mo=obs.interp(ma['RADIUS'],ma['M_NFW'])(ro)
        co=mo-bo
        assert np.min(np.diff(co))>0 and np.min(co)>0
        bf,completion=complete_mass(ro,bo)
        fit=least_squares(lambda p:np.log(np.exp(p[0])*NF(ro/np.exp(p[1]))/co),np.log([co[-1]/NF(hi/(r5/3)),r5/3]))
        amp,rs=np.exp(fit.x)
        raw=lambda r:amp*NF(np.asarray(r)/rs)
        rhoc=obs.critical_density(z)
        r2=brentq(lambda r:raw(r)+bf(r)-(4*np.pi/3)*200*rhoc*r**3,r5,4*r5)
        r=np.geomspace(.001,8*r2,12000)
        c=r2/rs; rd=.1*r2; eps=-(1+3*c)/(1+c)+r2/rd
        rho0=amp/(4*np.pi*rs**3)
        xx=r/rs
        rho=np.where(r<=r2,rho0/(xx*(1+xx)**2),rho0/(c*(1+c)**2)*(r/r2)**eps*np.exp(-(r-r2)/rd))
        stock=cumulative_trapezoid(4*np.pi*r*r*rho,r,initial=0)+amp*NF(r[0]/rs)
        b=bf(r); g=G*(stock+b)/r**2
        psi=cumulative_trapezoid(g[::-1],-r[::-1],initial=0)[::-1]+G*(stock[-1]+b[-1])/r[-1]
        # Invert the smooth density in its own plus the completed baryon potential.
        deriv_logrho=np.where(r<=r2,-1-2*xx/(1+xx),eps-r/rd)
        d1=-rho*deriv_logrho/(r*g)
        fp=PchipInterpolator(psi[::-1],d1[::-1]).derivative()
        eg=np.geomspace(psi[-1]*1.00001,psi[0]*.99999,1800)
        nodes,weights=np.polynomial.legendre.leggauss(160)
        u=.5*(nodes[None,:]+1)*np.sqrt(eg[:,None]-psi[-1])
        f=np.sum(fp(eg[:,None]-u*u)*weights[None,:],axis=1)*np.sqrt(eg-psi[-1])/(np.sqrt(8)*np.pi**2)
        # No silent clipping of a nonphysical Eddington DF.
        assert np.all(f>=0), (name,'negative Eddington DF',float(f.min()))
        rcheck=np.geomspace(.03*r5,1.5*r5,60); ps=np.interp(rcheck,r,psi)
        vg=np.linspace(0,1,1001)[None,:]*np.sqrt(2*ps[:,None])
        reconstructed=4*np.pi*np.trapezoid(vg**2*np.interp(ps[:,None]-vg**2/2,eg,f,left=0),vg,axis=1)
        expected=np.exp(np.interp(np.log(rcheck),np.log(r),np.log(np.maximum(rho,1e-300))))
        dferr=float(np.max(abs(reconstructed/expected-1)))
        assert dferr<.015,(name,'Eddington density mismatch',dferr)
        gb=G*bo/ro**2; target=bo/np.expm1(np.sqrt(gb/A0))
        idx=lambda val:float(np.interp(r5,ro,val))
        rec=dict(cluster=name,z=z,R500_kpc=r5,R200_model_kpc=r2,fit_stock_amplitude_Msun=float(amp),fit_stock_rs_kpc=float(rs),total_stock_Msun=float(stock[-1]),
                 NFW_stock_fit_rms_dex=float(np.sqrt(np.mean(np.log10(raw(ro)/co)**2))),NFW_stock_fit_max_total_mass_error=float(np.max(abs((raw(ro)+bo)/mo-1))),
                 stock_fit_mass_error_at_R500=float((raw(r5)+bf(r5))/idx(mo)-1),Eddington_density_recovery_max_relative_error=dferr,
                 observed_total_M500=idx(mo),observed_baryon_M500=idx(bo),observed_stock_M500=idx(co),HSE_header_error_M500=float(hd['ERR_M500'])*1e14,
                 RAR_total_over_observed_at_R500=idx(bo+target)/idx(mo),RAR_stock_over_observed_at_R500=idx(target)/idx(co),
                 observed_to_RAR_offset_dex_rms=float(np.sqrt(np.mean(np.log10(mo/(bo+target))**2))),completion=completion,radial_data_interval_kpc=[lo,hi])
        if name in lens:
            l=lens[name]; rat=l['M500']/l['M200']; y=(.4*rat)**(1/3)
            c200=brentq(lambda c:NF(c*y)/NF(c)-rat,.1,100)
            rwl=(l['M500']*1e14/(4*np.pi/3*500*rhoc))**(1/3)
            rswl=rwl/(y*c200)
            mw=lambda r:l['M500']*1e14*NF(np.asarray(r)/rswl)/NF(rwl/rswl)
            bw=float(bf(rwl)); targetwl=bw/np.expm1(np.sqrt(G*bw/(rwl*rwl*A0)))
            rec['independent_lensing']=dict(**l,R500_kpc=rwl,RAR_total_over_published_M500=(bw+targetwl)/(l['M500']*1e14),
                 HSE_at_lensing_R500_over_lensing_M500=float(obs.interp(ma['RADIUS'],ma['M_NFW'])(rwl)/(l['M500']*1e14)),
                 measured_baryons_cover_R500=bool(lo<=rwl<=hi))
        np.savez_compressed(inputs/(name+'.npz'),r=r,rho=rho,stock=stock,b=b,psi=psi,eg=eg,f=f,observed_r=ro,observed_b=bo,observed_total=mo,target_stock=target)
        report[name]=rec
        print(name,'fit max total error',round(rec['NFW_stock_fit_max_total_mass_error'],4),'RAR/observed',round(rec['RAR_total_over_observed_at_R500'],3),'DF error',dferr,flush=True)
    (inputs/'summary.json').write_text(json.dumps(report,indent=2,allow_nan=False))

if __name__=='__main__':main()
