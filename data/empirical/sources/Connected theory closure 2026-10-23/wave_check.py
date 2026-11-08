"""Periodic 1D wave check of the pressure branch at constant potential.
It tests the regular local principal dynamics, not a cosmological void or
multistream continuation. RK4 plus spectral differentiation; two resolutions.
"""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import least_squares
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent

def run(n,dt):
    L=3.;V=0.;r0=.75;v0=np.sqrt(1-4*(1-r0)**2);J0=L*r0*v0
    K=L/3;eps=1e-4
    x=2*np.pi*np.arange(n)/n;k=np.fft.fftfreq(n,1/n)
    deriv=lambda y:np.fft.ifft(1j*k*np.fft.fft(y)).real
    def state(phi,J):
        s=deriv(phi);q=abs(J)/L;sgn=np.sign(J)
        lower=.5*abs(s);upper=np.sqrt(1+s*s)
        canonical=q<=lower;dust=q>=upper
        lo=np.full(n,.5);hi=np.ones(n)
        for _ in range(44):
            rr=(lo+hi)/2
            f=rr*np.sqrt(np.maximum(0.,s*s+1-4*(1-rr)**2))
            mask=f<q;lo=np.where(mask,rr,lo);hi=np.where(mask,hi,rr)
        r=(lo+hi)/2;lam=L*r
        v=sgn*np.sqrt(np.maximum(0.,s*s+1-4*(1-r)**2))
        lam=np.where(canonical,L/2,lam);v=np.where(canonical,2*J/L,v)
        v=np.where(dust,sgn*upper,v);lam=np.where(dust,abs(J)/upper,lam)
        e=lam/2+2*np.maximum(L-lam,0.)**3/(3*L*L)
        e=np.where(canonical,L/3,e)
        X=(v*v-s*s)/2
        P=lam*X-e-V;rho=J*v-P
        return v,lam,s,rho,X
    def rhs(phi,J):
        v,lam,s,rho,X=state(phi,J)
        return v,deriv(lam*s)
    phi=eps*np.cos(x);J=np.full(n,J0);steps=round(10/dt)
    records=[]
    for z in range(steps+1):
        if z%10==0:
            v,lam,s,rho,X=state(phi,J)
            amp=2*np.mean(phi*np.cos(x))
            records.append([z*dt,amp,float(np.mean(rho)),float(np.mean(J)),float(X.min()),float(X.max())])
        if z==steps:break
        a,b=rhs(phi,J);c,d=rhs(phi+dt*a/2,J+dt*b/2)
        e,f=rhs(phi+dt*c/2,J+dt*d/2);g,h=rhs(phi+dt*e,J+dt*f)
        phi=phi+dt*(a+2*c+2*e+g)/6;J=J+dt*(b+2*d+2*f+h)/6
    arr=np.array(records);t=arr[:,0];amp=arr[:,1]/eps
    fit=least_squares(lambda p:p[0]*np.cos(p[1]*t)+p[2]*np.sin(p[1]*t)-amp,[1.,np.sqrt(.5),0.],
                      xtol=1e-13,ftol=1e-13,gtol=1e-13)
    report={'grid':n,'dt':dt,'fitted_frequency':float(fit.x[1]),'predicted_frequency':float(np.sqrt(.5)),
            'frequency_fractional_error':float(fit.x[1]/np.sqrt(.5)-1),
            'max_relative_energy_drift':float(np.max(abs(arr[:,2]/arr[0,2]-1))),
            'max_relative_current_drift':float(np.max(abs(arr[:,3]/arr[0,3]-1))),
            'min_X':float(arr[:,4].min()),'max_X':float(arr[:,5].max()),
            'min_total_energy_over_floor':float(arr[:,2].min()/K),
            'amplitude_fit_RMS':float(np.sqrt(np.mean(fit.fun**2)))}
    print(json.dumps(report),flush=True)
    return report,arr

def main():
    rows=[];traces=[]
    for n,dt in [(64,.004),(128,.002)]:
        r,a=run(n,dt);rows.append(r);traces.append(a)
    result={'scope':__doc__,'rows':rows,'frequency_refinement_difference':abs(rows[0]['fitted_frequency']-rows[1]['fitted_frequency'])}
    out=HERE/'results/local_waves.json'
    if out.exists():raise RuntimeError('Preserve previous result')
    out.write_text(json.dumps(result,indent=2),encoding='utf-8')
    fig,ax=plt.subplots(figsize=(7.5,3.5),layout='constrained')
    ax.plot(traces[-1][:,0],traces[-1][:,1]/1e-4,label='Nonlinear field evolution')
    ax.plot(traces[-1][:,0],np.cos(np.sqrt(.5)*traces[-1][:,0]),ls='--',label='Predicted sound mode')
    ax.set(xlabel='Time',ylabel='Perturbation / initial amplitude',title='Local wave test on the pressure branch')
    ax.legend();fig.savefig(HERE/'figures/local_wave.png',dpi=180);plt.close(fig)

if __name__=='__main__':main()
