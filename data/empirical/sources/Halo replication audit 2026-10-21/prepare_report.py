"""Assemble the final research report only after both eight-Gyr runs finish."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent;QUIET=HERE.parent/'Halo quiet realization 2026-10-21'
read=lambda name:json.loads((HERE/name).read_text())
assessment=read('replication_assessment.json');runs=assessment['runs'];matched=read('matched_shape_final.json')
ms={r['label']:r for r in matched['runs']};stream=read('stellar_streaming_final.json')
force=[json.loads((QUIET/'force_compatibility.json').read_text())[-1]]+read('final_force_checks.json')
assert all(r['end']==8 for r in runs)
allpass=all(r['descriptive_retention'] and r['numerical_pass'] for r in runs)
pages=[]
def p(t,s='body'):return {'type':s,'text':t}
def table(rows,widths):return {'type':'table','rows':rows,'widths':widths}
def picture(path,width,height):return {'type':'image','path':path,'width':width,'height':height}

if allpass:
    conclusion='The tilted candidate survives independent phase replication.'
    meaning=('Both new realizations retain substantial halo and stellar inclinations for eight billion years. '
       'Together with the original run, this establishes repeatability at the tested particle count within '
       'the same conditional stock and rigid-disk model. It is stronger evidence of dynamical feasibility, '
       'but it is not a proof of continuum stability or a completed prediction of the manuscript. '
       'All three also develop late precession drift and become rounder; a stationary configuration '
       'has not been demonstrated.')
else:
    conclusion='The phase replication test reveals sensitivity in the tilted candidate.'
    meaning=('At least one registered realization misses the descriptive retention condition or a numerical gate. '
       'The original successful-looking run therefore cannot establish robust survival at this particle count. '
       'The phase sensitivity is a numerical or dynamical issue to resolve; it is not by itself a rejection '
       'of every possible conserved-stock configuration.')
rows=[['Realization','Halo tilt<br/>10-40 kpc','Stellar tilt<br/>10-40 kpc','Stellar tilt<br/>6-60 kpc','Max energy<br/>error (%)']]
for r in runs:
    rows.append([r['label'],f"{r['final_halo_tilt']:.2f} deg",f"{r['final_stellar_tilt']:.2f} deg",
                 f"{ms[r['label']]['last']['tilt_p_q'][0]:.2f} deg",f"{100*r['energy_max']:.5f}"])
pages.append([p('Halo tilt:<br/>independent phase replication','title'),p(conclusion,'h1'),p(meaning),
    table(rows,[103,106,106,106,107]),
    p('Final values use the moments averaged over 7.5-8 Gyr, before computing their axes. '
      'The two radial cuts serve different purposes; neither replaces the other. Instantaneous snapshots '
      'and complete trajectories are retained in the data files.','small'),
    p('What was held fixed','h2'),
    p('All three runs contain 131,072 positive stock particles (65,536 inversion-pair representatives). '
      'The 1,072 positive orbit totals, stellar sample, force approximation, timestep and central '
      'regularization are identical. Only the stock phase draw changes: seeds 211033, 211034 and 211035. '
      'Each new seed passes the same initial force, torque, positivity and angular-momentum checks.'),
    p('The registered descriptive retention condition is a final halo tilt of at least 35 degrees '
      'and stellar tilt of at least 20 degrees in 10-40 kpc. It is not an observational confidence limit. '
      f"{assessment['retention_count']} of the three realizations satisfy it. No probability of success "
      'for a population is inferred from three seeds.'),
    p('The manuscript and a<sub>0</sub> are unchanged. Existing '
      'a<sub>0</sub> = 1.230729 x 10<super>-10</super> m s<super>-2</super>.','small')])

late=[]
for r in runs:
    h=r['final_two_Gyr'];late.append([r['label'],f"{min(x['halo'] for x in h):.1f}-{max(x['halo'] for x in h):.1f}",
        f"{min(x['stars'] for x in h):.1f}-{max(x['stars'] for x in h):.1f}",f"{r['precession_rate_relative_input']:.3f}"])
pages.append([p('Evolution, not a selected final snapshot','h1'),
    picture('replication_evolution.png',528,343.2),
    table([['Realization','Halo range, 6-8 Gyr','Stellar range, 6-8 Gyr','Precession / input']]+late,[103,145,145,135]),
    p('Ranges use all four final half-Gyr averages, in degrees. The rate is a descriptive linear fit '
      'to the disk precession phase over the full run. The lower-resolution and imposed-field curves '
      'are earlier references, not additional fixed-count phase replicas. Changes in inclination and '
      'azimuth can occur with excellent energy conservation; conservation alone does not establish equilibrium.','small'),
    p('The same stellar phase sample is used in every run. These are independent stock phase '
      'realizations conditional on one orbit fit, not independent merger histories or stellar fits.','small'),
    p('Snapshot variation matters: Replica 1 has a halo tilt of 33.50 degrees at the instantaneous '
      '8-Gyr checkpoint, compared with its registered final averaged value of 39.58 degrees. '
      'Passing the averaged retention condition does not imply that every snapshot passes it.','small')])

ref=matched['reference'];obs=[]
for r in runs:
    a=ms[r['label']]['last'];i=ms[r['label']]['last_instantaneous']
    obs.append([r['label'],f"{a['tilt_p_q'][0]:.2f}",f"{a['tilt_p_q'][1]:.4f}",f"{a['tilt_p_q'][2]:.4f}",
        f"{a['sum_squared_standardized_residuals']:.2f}",f"{i['sum_squared_standardized_residuals']:.2f}"])
pages.append([p('A more faithful stellar-shape comparison','h1'),
    p('The published comparison uses spherical-cut inertia moments over 6-60 kpc. Its density-axis '
      'parameters cannot be compared directly with inertia-axis ratios. I integrated the same parametric '
      'stellar density through that cut and propagated 1,000 independent Gaussian draws of the quoted '
      'shape uncertainties, following the published prescription. This supplementary diagnostic was '
      'added after the live runs began and does not change their registered outcomes.'),
    p(f"The mapped reference is tilt 25.39 +/- 3.16 degrees, p = {ref['mapped_mean_pq'][0]:.4f} +/- "
      f"{ref['mapped_sigma_pq'][0]:.4f}, q = {ref['mapped_mean_pq'][1]:.4f} +/- {ref['mapped_sigma_pq'][1]:.4f}. "
      'The quoted uncertainties describe the adopted target; they do not include every observational systematic.'),
    table([['Realization','Tilt','p','q','D, averaged','D, instant 8 Gyr']]+obs,[96,64,66,66,111,125]),
    p('D is the sum of the three squared residuals divided by the mapped variances, using major-axis '
      'inclination for the tilt diagnostic. It is a published-style summary, not a calibrated chi-square '
      'test or a full observational likelihood. Finite-tracer correlations, noncoplanarity and the '
      'survey selection function are not modeled. Both averaged and instantaneous results are shown.','small'),
    p('The original large run has a 24.38-degree stellar inclination in this cut and D = 0.96 for '
      'its final averaged shape. Its earlier 22.16-degree value is correct for 10-40 kpc, but using '
      'that number alone as the direct observational shortfall was too restrictive.'),
    p('Method source: <link href="https://arxiv.org/html/2510.00095v2#S3.SS4" color="#136f87">'
      'Dillamore &amp; Sanders (2026), Section 3.4 and equations 19-20</link>. '
      'The comparison here uses the stellar target and does not treat their halo-angle inference '
      'as a model-independent measurement.','small')])

orient=read('orientation_final.json')['runs']
pages.append([p('Radial shape and the third orientation angle','h1'),
    picture('radial_shapes.png',528,179.5),
    p('Global moments need not reproduce the adopted target in every radial bin. The figure shows '
      'all four bins used in the stored diagnostics, with the target processed through the same '
      'spherical cuts. It does not refit the radial profile.'),
    table([['Final snapshot','Minor-axis offset (deg)','Intermediate-axis elevation (deg)','Orientation-sensitive D']]+
       [[r['label'],f"{r['minor_axis_angle_to_target_after_major_azimuth_alignment_deg']:.2f}",
         f"{r['intermediate_axis_elevation_deg']:.2f}",f"{r['orientation_sensitive_D']:.2f}"] for r in orient],
       [110,136,150,132]),
    p('After aligning the overall stellar azimuth, the minor-axis angle detects departure from '
      'coplanarity. The intermediate-axis elevation would vanish for exact coplanarity with the '
      'disk. These are instantaneous 8-Gyr quantities, not the preceding averaged shape. '
      'The orientation-sensitive D replaces the inclination residual by the minor-axis offset; '
      'it remains a diagnostic, not a calibrated observational probability.','small'),
    p('Density shapes remain a separate question','h2'),
    p('For the analytic A = 0.3 stock target, the spherical-cut inertia ratio is 0.916. Its actual '
      'density-contour intercept ratio is about 0.78-0.81 between major-axis radii 10 and 40 kpc. '
      'Those are distinct definitions. The live tests do not establish that the evolved stock satisfies '
      'every Milky Way halo-shape constraint.'),
    p('The original run illustrates the distinction: its inclination-only instantaneous D is 0.47, '
      'whereas its 5.64-degree minor-axis offset raises the orientation-sensitive diagnostic to 3.51. '
      'The improved common-cut comparison is useful, but it is not a license to ignore the other axes.','small')])

pages.append([p('Shape and density remain visible','h1'),picture('replication_shapes.png',528,316.8),
    p('A nonzero eigenvalue gap is necessary for an orientation to be meaningful. The density '
      'diagnostic is the absolute cell-mass mismatch over 6-60 kpc, normalized by target mass in '
      'that range. It is not an observational likelihood and includes finite sampling noise.'),
    table([['Realization','Minimum halo gap','Final halo density L1','Final stellar density L1','Mass change &lt;20 kpc']]+
          [[r['label'],f"{r['halo_gap_min']:.3f}",f"{r['final_halo_density_L1']:.3f}",f"{r['final_stellar_density_L1']:.3f}",f"{100*r['mass_fractional_change']['20']:+.2f}%"] for r in runs],
          [103,105,108,112,100]),
    p('Initial moment checks show that fitting force, mean shape flow and torque does not make '
      'the discrete phase sample exactly stationary. The residual shape curvature appears in '
      'both the imposed analytic field and the live numerical field. It cannot be read as an '
      'instability growth rate without a separate response analysis.','small')])

frows=[]
for r,f in zip(runs,force):
    vmax=max(max(abs(a['speed_proxy_fractional_min']),abs(a['speed_proxy_fractional_max'])) for a in f['force_proxies'])
    frows.append([r['label'],f"{100*vmax:.2f}%",f"{100*f['vertical_even_fractional_range_vs_spherical_stock'][0]:+.2f}% to {100*f['vertical_even_fractional_range_vs_spherical_stock'][1]:+.2f}%",
                  f"{max(abs(v) for v in f['vertical_odd_potential_range_kms_squared']):.0f}"])
betas=[]
for r in stream['final']:
    c=r['cuts'][0];betas.append(f"{r['label']}: {c['beta_raw']:.4f} raw, {c['local_estimates'][1]['beta_count_corrected']:.4f} after local subtraction")
newdensity=read('density_reconstruction_final.json')['runs'];olddensity=read('density_reconstruction_reference.json')['runs'][-1]
density=[olddensity]+newdensity
negmax=max(r['shells'][1]['negative_fraction_of_total_stock'] for r in density)
smallneg=max(sum(s['negative_fraction_of_total_stock'] for s in r['shells']) for r in density)
pages.append([p('Compatibility and numerical safeguards','h1'),
    p(f"The largest sampled energy error is {100*max(r['energy_max'] for r in runs):.5f}%; "
      f"the largest angular-momentum error divided by disk angular momentum is {max(r['J_max'] for r in runs):.2e}. "
      'All weights remain positive. The earlier timestep and central-regularization comparisons are '
      'preserved; this audit isolates phase variation at their baseline settings.'),
    table([['Realization','Max speed-proxy shift','Even vertical change','Max odd term']]+frows,[103,116,180,129]),
    p('Speed proxies sample 8.2-60 kpc and are compared with the original spherical stock plus '
      'baryons. Vertical values use R = 8.2 kpc and z = +/-1.1 kpc. The odd term is the half-difference '
      'of the two potentials, in (km/s)<super>2</super>. These are force comparisons, not new rotation-curve '
      'or vertical-equilibrium fits. The odd term is not removed by the small even change.','small'),
    p('Stellar velocity anisotropy','h2'),
    p('At the final instantaneous snapshot, the 6-24 kpc radial anisotropy changes little when '
      'coherent local motion is subtracted using 32 angular cells. Inversion partners are counted once. '
      + '; '.join(betas)+'. The coarse bins do not resolve all possible streaming.'),
    p('Positivity of the force reconstruction','h2'),
    p(('No negative reconstructed density was found on the sampled 5-60 kpc integration grids. ' if negmax==0 else
       f'The largest sampled negative effective mass in 5-60 kpc is {negmax:.3g} of the stock mass. ')+
      f'Across 0.2-160 kpc, the largest integrated negative reconstruction artifact is {smallneg:.3g} of '
      'the stock mass. These are finite multipole/spline artifacts, not negative particle masses. '
      'The analytic Laplacian was checked against numerical force divergence. Positivity between '
      'sampled points or outside this domain is not proved.','small'),
    p('Future phases remain noisier than the initial fit','h2'),
    p('Transporting each frozen phase quadrature through the prescribed field produces substantial '
      'fluctuations relative to the weak transverse force. Initial quietness therefore does not '
      'persist automatically. Replication at fixed N tests sensitivity to this effect; it does '
      'not make the effect vanish.','small')])

multi=[read('higher_multipole_reference.json')['runs'][-1]]+read('higher_multipole_final.json')['runs']
mh=[]
for r in multi:
    mh.append([r['label'],f"{100*max(v['l4_to_l6_total_fraction'] for v in r['rows']):.2f}%",
       f"{100*max(v['l4_to_l6_transverse_fraction'] for v in r['rows']):.1f}%",
       f"{100*max(v['l6_to_l8_transverse_fraction'] for v in r['rows']):.1f}%"])
pages.append([p('Repeatability is not force convergence','h1'),
    picture('force_resolution.png',528,211.2),
    table([['Realization','4 to 6 / total stock force','4 to 6 / transverse','6 to 8 / transverse']]+mh,[103,145,140,140]),
    p('The table gives maximum RMS fractional changes over the five tested radii, using final '
      'frozen snapshots. Each added angular order includes its complete multiplet. The radial '
      'spline and regularization are unchanged. An independent implementation reproduces the '
      'original order-four force before adding the higher modes.','small'),
    p('The supporting transverse field is much weaker than the radial field. Consequently a small '
      'change relative to total stock acceleration can be a substantial change in the force that '
      'supports the tilted figure. The omitted modes include both physical deformation and '
      'finite-particle sampling noise; higher-order noise is already present initially.'),
    p('The evidence therefore does not establish convergence of the live trajectories with angular '
      'order. Increasing the angular order at fixed particle count also admits more sampling noise. '
      'A useful next numerical comparison must control both particle count and force resolution, '
      'with a common phase construction or sufficient independent replicas.'),
    p('None of these diagnostics changes the registered runs, selects a new phase seed, adjusts '
      'the physical target, or changes a<sub>0</sub>. They limit how strongly the replication result '
      'can be interpreted.','small')])

ring=read('disk_torque_reference.json')['runs'][-1]
rr=[r for r in ring['rings'] if r['radius_kpc'] in [6.,8.2,15.,20.]]
pages.append([p('What this closes, and what remains','h1'),
    p('The route is already present in the manuscript','h2'),
    p('Section 16 identifies a conserved, assembly-shaped stock as the way to sustain a tilted '
      'potential. Appendix O.3 supplies positive stock continuity, a budget and velocity stress, '
      'while explicitly leaving the full transport and common variational coupling incomplete. '
      'The new work makes one kinetic realization concrete. It does not amend the aligned static '
      'solution, which still lacks the required long-lived tilted potential.'),
    p('The next physical test concerns the disk','h2'),
    table([['Radius (kpc)','Uncoupled ring rate (rad/Gyr)','Difference from rigid bulk (rad/Gyr)']]+
          [[f"{r['radius_kpc']:g}",f"{r['ring_rate_magnitude_rad_Gyr']:.3f}",f"{r['rate_difference_from_rigid_bulk_rad_Gyr']:.3f}"] for r in rr],
          [108,210,210]),
    p('Values refer to the original large run at 8 Gyr. They are the initial precession tendencies '
      'of thin test rings in its field. Different radii require internal disk torques to maintain '
      'common motion. Disk self-gravity and bending response were omitted from this diagnostic, '
      'so it does not predict a warp amplitude or establish a disk instability.','small'),
    p('Remaining closure','h2'),
    p('A controlled particle-number comparison and higher angular/radial force resolution remain '
      'necessary. A deformable disk and finite director/polarization response remain necessary for '
      'the full theory. A physically selected transport or relaxation law, and formation of the '
      'fitted orbit distribution, have not been derived. Repeating one tuned orbit family cannot '
      'settle those questions.'),
    p('The next numerical target is the shared drift','h2'),
    p('The fitted precession rates are 0.918-0.925 of the construction rate across all three seeds. '
      'The late azimuth slip and declining halo shape gap are also shared. This points to a common '
      'effect that more phase draws alone will not resolve. The next test should separate a mismatch '
      'in the constructed relative equilibrium, systematic finite-sampling effects and a physical '
      'collective mode, while controlling particle count and angular force order. No instability '
      'growth rate or uniquely identified cause has been established.','small'),
    p('Reproducibility','h2'),
    p('PROTOCOL.txt fixes the seeds and gates. run_replica.py drives unchanged stage copies. '
      'replication_assessment.json records every outcome; matched_shape_final.json supplies the '
      'supplementary shape comparison. Half-Gyr checkpoints, source snapshots, diagnostic code '
      'and a final hash manifest are preserved alongside this report. No prior results were deleted.','small')])

content={'pages':pages,'conclusion':conclusion,'interpretation':meaning}
assert not (HERE/'REPORT CONTENT.json').exists()
(HERE/'REPORT CONTENT.json').write_text(json.dumps(content,indent=2))
plain=[conclusion,meaning,'','Final 7.5-8 Gyr averaged moments (halo, stars; 10-40 kpc):']
plain += [f"{r['label']}: {r['final_halo_tilt']:.3f}, {r['final_stellar_tilt']:.3f} degrees" for r in runs]
plain += ['', 'Read: Halo tilt - independent phase replication audit.pdf',
          'Manuscript and a0 unchanged. See PROTOCOL.txt and INTERPRETATION RULES.txt.']
(HERE/'START HERE.txt').write_text('\n'.join(plain)+'\n')
print(conclusion)
