import json,glob,os,numpy as np
R='/tmp/claude-0/c28/sim'; inp=json.load(open(R+'/inputs/summary.json'))
G=4.30091e-6; A0=1.2307e-10*3.0857e19/1e6
def load(c,l):
    d=[x for x in glob.glob(R+f'/runs/*_{c}_*_{l}') if os.path.exists(x+'/summary.json')]
    if not d: return None
    return json.load(open(d[-1]+'/summary.json')),np.load(d[-1]+'/profiles_and_state.npz'),json.load(open(R+f'/corelogs/{c}_{l}.json'))
out=[]
for c in ['A85','A1795','A2029','A2142','A2319','A644','ZW1215']:
    C=load(c,'sc_control'); L=load(c,'sc_labeled')
    if not C or not L: continue
    s,p,lg=L; cs,cp,cl=C; r5=inp[c]['R500_kpc']; r=p['r_kpc']
    at=lambda f:float(p['late_mean_total_mass'][np.argmin(abs(r-f*r5))]/cp['late_mean_total_mass'][np.argmin(abs(r-f*r5))])
    t=np.array(lg['t']); late=t>=8
    def ratio(key):
        a=np.array(lg[key])[late].mean(); b=np.array(cl[key])[late].mean(); return a/b, a, b
    rd_=ratio('n_rd'); r2_=ratio('n_2rd'); car=np.array(lg['M_carried']); carc=np.array(cl['M_carried'])
    # law stock of the central carrier at r_d (3D stars)
    Mrec=lg['Mrec_rd']; rd=lg['rd']; x=np.sqrt(G*Mrec/rd**2/A0); law=Mrec/np.expm1(x)
    row=dict(cluster=c,R500=at(1),r03=at(.3),r01=at(.1),core_rd=rd_[0],n_rd=rd_[2],core_2rd=r2_[0],n_2rd=r2_[2],
             carried_start=car[0],carried_late=car[late].mean(),carried_ctrl_late=carc[late].mean(),law_stock=law,
             stock_rd_ctrl=rd_[2]*lg['m'],acc=s['accepted_contacts'],spent=s['initial_register_specific_km2_s2']-s['final_register_specific'])
    out.append(row)
    print(f"{c:7s} R500 {row['R500']:.4f} 0.3 {row['r03']:.4f} 0.1 {row['r01']:.4f} | <r_d {row['core_rd']:.3f} (n {row['n_rd']:.0f}, ±{1/np.sqrt(row['n_rd']):.2f}) <2r_d {row['core_2rd']:.3f} (n {row['n_2rd']:.0f}) | carried late {row['carried_late']:.2e} ctrl {row['carried_ctrl_late']:.2e} law {law:.2e} stock(<r_d) {row['stock_rd_ctrl']:.2e} acc {row['acc']}")
json.dump(out,open('/tmp/claude-0/c28/results_sc.json','w'),indent=1)
