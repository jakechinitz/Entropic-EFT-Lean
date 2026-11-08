"""Independent unit, normalization, geometry and preservation checks."""
from pathlib import Path
import sys,json,hashlib
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'dependencies'))
import numpy as np
from astropy.cosmology import FlatLambdaCDM
from astropy.io import fits
from astropy.wcs import WCS
import radial_analysis as radial

r=json.loads((ROOT/'results/radial_summary.json').read_text())
b=json.loads((ROOT/'results/bullet_targets.json').read_text())
checks={}
checks['12_clusters_7_stellar_5_independent_lensing']=(len(r['clusters'])==12 and sum(x['has_stellar_profile'] for x in r['clusters'].values())==7 and len(r['lensing'])==5)
checks['stellar_projection_075_at_R500']=abs(radial.projection_fraction(radial.X500)-.75)<1e-10
checks['projection_fraction_between_zero_and_one']=all(0<radial.projection_fraction(x)<1 for x in [.001,.1,1,10,100])
cosmo=FlatLambdaCDM(H0=70,Om0=.3)
checks['critical_density_independent_astropy']=abs(radial.critical_density(.09)/cosmo.critical_density(.09).to('Msun/kpc3').value-1)<1e-10
checks['cohort_ratio_matches_prior']=abs(r['k_stock_per_cohort_baryon']-json.loads((ROOT.parent/'Unified empirical program 2026-10-23/results/cluster_cohort_audit.json').read_text())['saturated_surviving_stock_per_cohort_baryon'])<1e-12
checks['no_negative_required_NFW_shells']=all(x['negative_required_stock_shells_NFW']==0 for x in r['clusters'].values())
checks['forward_A644_failure_retained']=r['clusters']['A644']['negative_required_stock_shells_forward']==4
identities=[];hse=[];apertures=[]
for c,l in r['lensing'].items():
    hd,ma,ga,rg,st=radial.profile(c);rho=radial.critical_density(hd['REDSHIFT'])
    for p in l['coextensive_prediction']:
        rp=p['R500_kpc'];mp=p['M500_1e14']*1e14
        identities.append(abs(mp/(4*np.pi/3*500*rho*rp**3)-1))
        baryon=float(radial.interp(rg,ga['MGAS'])(rp)+p['stellar_multiplier']*radial.stellar(st,rp,hd['R500']))
        identities.append(abs(mp/((1+radial.K)*baryon)-1))
    hse.append(abs(r['clusters'][c]['R500']['M_NFW_Msun']/(hd['M500']*1e14)-1))
checks['self_consistent_overdensity_and_budget']=max(identities)<1e-10
checks['NFW_profile_matches_M500_header']=max(hse)<.002
checks['bullet_non_gas_is_total_minus_gas']=all(abs((a['gas_projected_Msun']+a['nongas_projected_Msun'])/a['total_projected_Msun']-1)<1e-12 for a in b['apertures'])
checks['bullet_aperture_pixel_convergence_below_03_percent']=max(x['max_grid_change_total_fraction'] for x in b['pixel_convergence'])<.003
checks['bullet_halo_offset_reproduces_published_4kpc_rounding']=round(b['subcluster_fitted_halo_BCG_offset_kpc'])==4
with fits.open(ROOT/'source_data/bullet/v1/best_fit_model/bulletclu-kappa-best-50mas.fits') as h:
    w=WCS(h[0].header)
    q=np.array(list(b['BCG_positions_fk5_deg'].values()))
    pix=w.all_world2pix(q,0);back=w.all_pix2world(pix,0)
    checks['bullet_WCS_roundtrip']=np.max(abs(q-back))<1e-9
    checks['BCGs_inside_map']=bool(np.all(pix>0) and np.all(pix<8000))
sha=[]
for f in (ROOT/'source_records').glob('*.json'):
    d=json.loads(f.read_text())
    if isinstance(d,dict) and 'sha256' in d:
        p=ROOT/d['path'];sha.append(hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==d['sha256'])
checks['download_hashes_match']=all(sha) and len(sha)==3
checks={key:bool(value) for key,value in checks.items()}
result={'all_passed':all(checks.values()),'checks':checks,'max_M500_header_fraction':max(hse),
        'max_identity_error':max(identities),'interpretation':'Numerical/data-handling checks, not validation of the theory or physical equilibrium.'}
(ROOT/'results/validation.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
assert result['all_passed']
