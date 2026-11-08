import json,numpy as np,matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
names=['A85','A1795','A2029','A2142','A2319','A644','ZW1215']
gpt={'A85':(0.787,0.424,0.351),'A1795':(0.726,0.352,0.295),'A2029':(0.666,0.345,0.290),'A2142':(0.774,0.440,0.331),'A2319':(0.746,0.319,0.209),'A644':(0.697,0.330,0.234),'ZW1215':(0.547,0.404,0.366)}
r2=json.load(open('/tmp/claude-0/c28/results_rows.json'))
def pick(lab,k=3): return {r['cluster']:(r['R500'],r['r03'],r['r01']) for r in r2 if r['label']==lab and r['k']==k}
sup=pick('support'); der=pick('derived')
r10=json.load(open('/tmp/claude-0/c28/results10k.json'))
full={r['cluster']:(r['R500'],r['r03'],r['r01']) for r in json.load(open('/tmp/claude-0/c28/results_sc.json'))}
sup10={r['cluster']:(r['R500'],r['r03'],r['r01']) for r in r10 if r['rule']=='support10k'}
rules=[('no switch, galaxy-scaled work (GPT)',gpt,'#c0392b','o'),('support only, galaxy-scaled work',sup,'#e67e22','s'),
       ('support only, cell work',sup10,'#8e44ad','^'),('support + carried stock + cell work',full,'#2471a3','D')]
fig,axs=plt.subplots(1,3,figsize=(13,4.2),sharey=True)
for j,(ax,lab) in enumerate(zip(axs,['$R_{500}$','$0.3R_{500}$','$0.1R_{500}$'])):
    for i,(nm,d,col,mk) in enumerate(rules):
        y=[d[n][j] for n in names if n in d]; x=np.arange(len(y))+(i-1.5)*0.15
        ax.scatter(x,y,color=col,marker=mk,s=28,label=nm if j==0 else None,zorder=3)
    ax.axhline(1,color='k',lw=.8,ls=':'); ax.set_xticks(range(7)); ax.set_xticklabels(names,rotation=45,fontsize=8)
    ax.set_title('mass inside '+lab+' / no-contact control',fontsize=10); ax.set_ylim(0,1.12); ax.grid(alpha=.25)
axs[0].legend(fontsize=7.5,loc='lower left',frameon=True)
plt.tight_layout(); plt.savefig('/tmp/claude-0/c28/note/switch_runs.png',dpi=170)
print('ok')
