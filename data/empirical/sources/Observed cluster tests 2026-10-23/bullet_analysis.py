"""Reduce released Bullet maps to empirical targets; no theory map is fitted."""
from pathlib import Path
import sys,json,re
ROOT=Path(__file__).resolve().parent
OUT=ROOT
sys.path.insert(0,str(ROOT/'dependencies'))
import numpy as np
from astropy.io import fits
from astropy.wcs import WCS
from astropy.cosmology import FlatLambdaCDM
from scipy.ndimage import map_coordinates,gaussian_filter
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

DATA=ROOT/'source_data/bullet/v1/best_fit_model'
G=4.30091727003628e-6
C=299792.458
COSMO=FlatLambdaCDM(H0=70,Om0=.3)
DL=COSMO.angular_diameter_distance(.296).to('kpc').value
SCALE=DL*np.pi/(180*3600)
SIGCRIT=C*C/(4*np.pi*G*DL)  # Dls/Ds=1, explicitly documented in release README

def parse_potentials(text):
    out={}
    for name,body in re.findall(r'^potential\s+(\S+)\s*\n(.*?)^\s*end\s*$',text,re.M|re.S):
        d={}
        for line in body.splitlines():
            a=line.split()
            if len(a)==2:
                try:d[a[0]]=float(a[1])
                except ValueError:pass
        out[name]=d
    return out

def run():
    with fits.open(DATA/'bulletclu-kappa-best-50mas.fits') as h:
        total=h[0].data.copy();head=h[0].header.copy()
    with fits.open(DATA/'xray_kappa_dsdls1.fits') as h:
        gas=h[0].data.copy();gh=h[0].header.copy()
    w=WCS(head);wg=WCS(gh)
    pots=parse_potentials((DATA/'bestopt.par').read_text())
    ra0,dec0=104.658712,-55.957146
    # Use the catalogue's explicit FK5 positions for the BCGs (commented rows
    # because these galaxies have separate potentials in the released model).
    catalogue=(DATA/'cm_v6.fk5.dat').read_text().splitlines()
    bcg={}
    for code,catid in [('BCG1','1'),('BCG2','3'),('BCG3','4')]:
        line=next(l for l in catalogue if l.startswith('#'+catid+' '))
        a=line[1:].split();bcg[code]=(float(a[1]),float(a[2]))
    # Header RA/DEC tangent plane relative to the same supplied catalogue.
    def at_gas(px,py):
        ra,dec=w.all_pix2world(px,py,0)
        gx,gy=wg.all_world2pix(ra,dec,0)
        return map_coordinates(gas,[gy,gx],order=1,mode='constant',cval=np.nan)
    pixarea=abs(np.linalg.det(w.pixel_scale_matrix))*(np.pi/180*DL)**2
    rows=[]; convergence=[]
    for code,(ra,dec) in bcg.items():
        cx,cy=w.all_world2pix(ra,dec,0)
        for radius in [60.,150.]:
            # Local tangent-plane area variation is negligible across these apertures.
            pixrad=radius/np.sqrt(pixarea)
            xmin=max(0,int(cx-pixrad-2));xmax=min(total.shape[1],int(cx+pixrad+3))
            ymin=max(0,int(cy-pixrad-2));ymax=min(total.shape[0],int(cy+pixrad+3))
            values=[]
            for step in [1,2,4]:
                yy,xx=np.mgrid[ymin:ymax:step,xmin:xmax:step]
                area=step*step*pixarea
                mask=(xx-cx)**2+(yy-cy)**2<=pixrad**2
                gt=at_gas(xx,yy);assert np.isfinite(gt[mask]).all()
                mt=float(np.sum(total[yy,xx][mask],dtype=np.float64)*area*SIGCRIT)
                mg=float(np.sum(gt[mask],dtype=np.float64)*area*SIGCRIT)
                values.append((mt,mg))
            mt,mg=values[0]
            # Non-gas contains dark/stock AND stellar mass; do not label all as stock.
            row={'centre':code,'radius_kpc':radius,'total_projected_Msun':mt,
                 'gas_projected_Msun':mg,'nongas_projected_Msun':mt-mg,
                 'gas_fraction':mg/mt,'coextensive_gas_only_to_total':(1+5.1760752079627395)*mg/mt,
                 'stellar_Msun_needed_for_coextensive_equality':mt/(1+5.1760752079627395)-mg}
            rows.append(row)
            convergence.append({'centre':code,'radius_kpc':radius,
                'max_grid_change_total_fraction':max(abs(v[0]/mt-1) for v in values),
                'max_grid_change_gas_fraction':max(abs(v[1]/mg-1) for v in values)})
    # Empirical halo-centre/BCG alignment from fitted components, not total-map peak.
    p3,p6=pots['O3'],pots['O6']
    halo_offset=SCALE*np.hypot(p3['x_centre']-p6['x_centre'],p3['y_centre']-p6['y_centre'])
    # Gas peak nearest the subcluster: native 1.968-arcsec map, inside 200 kpc.
    yy,xx=np.indices(gas.shape);ra,dec=wg.all_pix2world(xx,yy,0)
    bx,by=bcg['BCG3'];dist=SCALE*np.hypot((ra-bx)*3600*np.cos(np.deg2rad(by)),(dec-by)*3600)
    peak=np.unravel_index(np.argmax(np.where(dist<200,gas,-np.inf)),gas.shape)
    gasoffset=float(dist[peak])
    # Common map overlay, downsample only for plotting.
    step=12;yy,xx=np.mgrid[0:total.shape[0]:step,0:total.shape[1]:step]
    ra,dec=w.all_pix2world(xx,yy,0)
    X=(ra0-ra)*3600*np.cos(np.deg2rad(dec0))*SCALE
    Y=(dec-dec0)*3600*SCALE
    gt=at_gas(xx,yy);tt=total[yy,xx];ng=tt-gt
    fig,axs=plt.subplots(1,2,figsize=(11,4.8),sharex=True,sharey=True)
    for ax,arr,title in zip(axs,[tt,ng],['Released total lensing mass','Released total minus supplied gas']):
        im=ax.pcolormesh(X,Y,arr*SIGCRIT/1e9,shading='auto',cmap='Blues',vmin=0,vmax=5)
        ax.contour(X,Y,gt,levels=np.array([.1,.25,.5,.75])*np.nanmax(gt),colors='#ba4c32',linewidths=1)
        for name,(a,d) in bcg.items():
            x=(ra0-a)*3600*np.cos(np.deg2rad(dec0))*SCALE;y=(d-dec0)*3600*SCALE
            ax.scatter(x,y,c='#252a30',marker='+',s=80);ax.text(x+12,y+20,name,fontsize=8)
        ax.set_title(title,fontsize=11);ax.set_aspect('equal');ax.set_xlim(-220,1000);ax.set_ylim(-300,550)
        ax.set_xlabel('West of BCG1 reference [kpc]')
    axs[0].set_ylabel('North [kpc]');fig.colorbar(im,ax=axs,shrink=.7,label=r'$\Sigma\ [10^9\ M_\odot\ {\rm kpc}^{-2}]$')
    fig.suptitle('Bullet Cluster: observational targets; red contours = gas',fontsize=12)
    fig.savefig(OUT/'figures/bullet_observed_maps.png',dpi=190,bbox_inches='tight');plt.close(fig)
    result={'release':'CANUCS Bullet v1, README 17 March 2026; Rihtarsic et al. 2601.22245v2',
            'cosmology':{'H0':70,'Om0':.3,'z_lens':.296},'Dls_over_Ds':1,
            'angular_diameter_distance_kpc':DL,'kpc_per_arcsec':SCALE,
            'Sigma_crit_Msun_per_kpc2':SIGCRIT,'pixel_area_kpc2':pixarea,
            'map_shape':list(total.shape),'gas_native_pixel_kpc':abs(gh['CDELT1'])*3600*SCALE,
            'BCG_positions_fk5_deg':bcg,'subcluster_fitted_halo_BCG_offset_kpc':halo_offset,
            'subcluster_native_gas_peak_BCG_offset_kpc':gasoffset,
            'apertures':rows,'pixel_convergence':convergence,
            'limits':['A best-fit reconstruction is an empirical target, not a theory prediction.',
                      'Total minus gas still contains stars. Galaxy lens halos must not be subtracted as purely stellar masses.',
                      'Apertures overlap or include other components and are not isolated halo virial masses.',
                      'No map covariance or model-systematic marginalization; no fit significance or contact-rate bound.',
                      'The previous idealized simulation has the wrong observational resolution and unfitted initial conditions for the 4-kpc alignment.']}
    (OUT/'results/bullet_targets.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:result[k] for k in ['kpc_per_arcsec','Sigma_crit_Msun_per_kpc2','subcluster_fitted_halo_BCG_offset_kpc','subcluster_native_gas_peak_BCG_offset_kpc','apertures','pixel_convergence']},indent=2))

if __name__=='__main__':
    if len(sys.argv)>1:
        OUT=Path(sys.argv[1]).resolve()
        (OUT/'results').mkdir(parents=True,exist_ok=False)
        (OUT/'figures').mkdir(exist_ok=False)
    run()
