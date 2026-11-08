from pathlib import Path
import json,argparse
import numpy as np
from scipy.ndimage import gaussian_filter,maximum_filter
from scipy.signal import find_peaks
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
GRID=np.linspace(-8,8,321);DX=GRID[1]-GRID[0];CENTRE=(GRID[1:]+GRID[:-1])/2
def mapping(x,w,width=.3):
    return gaussian_filter(np.histogram2d(x[:,0],x[:,1],bins=(GRID,GRID),weights=w)[0],width/DX)/DX**2
def peak(a):
    i,j=np.unravel_index(np.argmax(a),a.shape);return np.array([CENTRE[i],CENTRE[j]])
def evaluate(tag):
    folder=HERE/'results'/tag;r=json.loads((folder/'result.json').read_text());a=np.load(folder/'history.npz')
    centres=np.array([x['core_centres'] for x in r['history']]);dist=np.linalg.norm(centres[:,0]-centres[:,1],axis=1)
    pks=find_peaks(-dist,distance=5)[0];ip=int(pks[0] if len(pks) else np.argmin(dist))
    target=a['time'][ip]+2;idx=int(np.argmin(abs(a['time']-target)))
    assert abs(a['time'][idx]-target)<.11, 'Need longer run to reach the declared comparison epoch'
    x=a['x'][idx];m=a['m'];kind=a['kind'];cohort=a['cohort'];u=a['u'][idx]
    rows=[]
    for c in [0,1]:
        maps=[mapping(x[(kind==j)&(cohort==c)],m[(kind==j)&(cohort==c)]) for j in [0,1,2]]
        peaks=[peak(b) for b in maps];dsg=float(np.linalg.norm(peaks[0]-peaks[2]));dsstar=float(np.linalg.norm(peaks[0]-peaks[1]))
        com=[np.average(x[(kind==j)&(cohort==c)],axis=0,weights=m[(kind==j)&(cohort==c)]).tolist() for j in [0,1,2]]
        rows.append({'cohort':c,'projected_peaks_stock_stars_gas':[p.tolist() for p in peaks],
                     'stock_gas_peak_distance':dsg,'stock_stars_peak_distance':dsstar,'centres_of_mass_stock_stars_gas':com,
                     'stock_mass':float(sum(m[(kind==0)&(cohort==c)])),
                     'baryon_mass':float(sum(m[(kind!=0)&(cohort==c)]))})
    total=mapping(x,m);gas=kind==2
    if len(a['rho_gas'][idx]):emission=m[gas]*a['rho_gas'][idx]*np.sqrt(u[gas])
    else:emission=m[gas]
    gm=mapping(x[gas],emission)
    top=np.argwhere((total==maximum_filter(total,size=21))&(total>.05*total.max()))
    top=sorted(top,key=lambda ix:total[tuple(ix)],reverse=True)
    totalpeaks=[]
    for ix in top:
        pp=np.array([CENTRE[ix[0]],CENTRE[ix[1]]])
        if all(np.linalg.norm(pp-qq)>1 for qq in totalpeaks):totalpeaks.append(pp)
        if len(totalpeaks)==2:break
    result={'tag':tag,'pericentre_time':float(a['time'][ip]),'evaluation_time':float(a['time'][idx]),
            'core_separation_at_pericentre':float(dist[ip]),'core_separation_at_evaluation':float(dist[idx]),
            'cohorts':rows,'global_total_mass_peaks':[p.tolist() for p in totalpeaks],
            'contact':r['contact'],'max_energy_error':r['max_energy_error_over_initial_binding'],
            'max_momentum_error':r['max_momentum_error'],'max_angular_error':r['max_angular_error'],
            'minimum_clock_surplus':r['minimum_clock_surplus'],'settings':r['settings']}
    return result,(a,r,idx,total,gm)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--tag',required=True);ap.add_argument('runs',nargs='+');args=ap.parse_args()
    rows=[];all_data=[]
    for name in args.runs:
        row,data=evaluate(name);rows.append(row);all_data.append(data)
    with (HERE/(args.tag+'.json')).open('x',encoding='utf-8') as f:json.dump(rows,f,indent=2)
    fig,axs=plt.subplots(1,len(rows),figsize=(4*len(rows),4.2),layout='constrained',squeeze=False)
    for ax,row,(a,r,idx,tot,gm) in zip(axs[0],rows,all_data):
        ax.imshow(np.log10(gm.T/gm.max()+1e-4),origin='lower',extent=[-8,8,-8,8],vmin=-3,vmax=0,cmap='magma')
        ax.contour(CENTRE,CENTRE,tot.T,levels=tot.max()*np.array([.15,.3,.5,.75]),colors='cyan',linewidths=.8)
        x=a['x'][idx];stars=a['kind']==1;ax.scatter(x[stars,0],x[stars,1],s=2,c='white',alpha=.5)
        ax.set(xlim=(-4,5),ylim=(-3,3),xlabel='x / a',ylabel='y / a',title=f"{row['tag']}\nt = {row['evaluation_time']:.1f}",aspect='equal')
    fig.suptitle('Baryonic emission proxy (color), total mass (cyan), stellar tracers (white)')
    fig.savefig(HERE/'figures'/(args.tag+'_maps.png'),dpi=180);plt.close(fig)
    fig,axs=plt.subplots(1,3,figsize=(12,3.5),layout='constrained')
    for row,(a,r,idx,tot,gm) in zip(rows,all_data):
        t=a['time'];cc=np.array([z['core_centres'] for z in r['history']]);sep=np.linalg.norm(cc[:,0]-cc[:,1],axis=1)
        axs[0].plot(t,sep,label=row['tag'])
        e=np.array([z['energy'] for z in r['history']]);axs[1].plot(t,(e-e[0])/abs(r['base']['potential']))
        axs[2].plot(t,np.sum(a['clock'],axis=1)-np.sum(a['clock'][0]))
    axs[0].set(xlabel='Time',ylabel='Galaxy-core separation');axs[0].legend(fontsize=7)
    axs[1].set(xlabel='Time',ylabel='Energy drift / initial binding');axs[2].set(xlabel='Time',ylabel='Change in stored work energy')
    for ax in axs:ax.grid(alpha=.2)
    fig.savefig(HERE/'figures'/(args.tag+'_histories.png'),dpi=180);plt.close(fig)
    print(json.dumps([{k:r[k] for k in ['tag','pericentre_time','evaluation_time','core_separation_at_evaluation','cohorts']} for r in rows]))
if __name__=='__main__':main()
