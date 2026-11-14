from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,html,shutil
import numpy as np
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]

def read(name):return json.loads((HERE/'results'/name).read_text(encoding='utf-8'))

def main():
    base=read('adaptive_boundary_base.json');fine=read('adaptive_boundary_refined.json')
    joint=read('connected_checks.json');waves=read('local_waves.json');stock=read('stock_contact.json')
    leanfile=sorted((HERE/'results').glob('lean_*.json'))[-1]
    lean=json.loads(leanfile.read_text(encoding='utf-8'));log=Path(lean['log']).read_text(encoding='utf-8')
    assert lean['success'] and not lean['contains_sorry'] and 'sorryAx' not in log
    assert len(re.findall('depends on axioms:',log))==lean['theorems']
    keys=['today_baryon_contrast','today_clock_velocity','today_current_over_background_stock',
          'today_dark_energy_over_background']
    diffs=[abs(x[k]-y[k]) for x,y in zip(base['patches'],fine['patches']) for k in keys]
    worst=max(diffs);constraint=max(x['max_friedmann_residual_over_Hbg2'] for x in fine['patches'])
    assert constraint<5e-8 and worst<1e-6
    assert all(p['min_current_over_background']>=0 and p['min_clock_velocity']>=0 and
               p['min_total_dark_energy_over_floor']>=1-1e-10 and p['vacuum_monotone_in_test']
               and p['max_cs2']<=1+1e-12 for p in fine['patches'])
    assert fine['max_cutoff_over_background_stock_through_today']<.031
    assert all(row['F_times_delay_times_H']>=4-1e-8 for row in joint['noise']['two_pole_rows'])
    assert all(row['min_total_force_over_instantaneous_equilibrium']>=1-1e-8
               for row in joint['response']['rows'] if row['initial_condition']=='equilibrated')
    assert all(abs(row['frequency_fractional_error'])<1e-7 for row in waves['rows'])
    # Total-energy normalization hides the small size of the wave energy.
    # At the stated background r=3/4, rho_background/K=2 exactly.
    wave_bounds=[]
    for row in waves['rows']:
        ratio=row['min_total_energy_over_floor']
        bound=row['max_relative_energy_drift']*ratio/(ratio-2)
        wave_bounds.append(bound)
    manifest=json.loads((HERE/'source_records/input_manifest.json').read_text(encoding='utf-8'))
    changed=[]
    for row in manifest['inputs']:
        p=ROOT/row['path']
        if hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256']:changed.append(row['path'])
    assert not changed,changed
    report={'checked_utc':datetime.now(timezone.utc).isoformat(),'success':True,
        'input_files_unchanged':len(manifest['inputs']),'changed_inputs':changed,
        'Lean':lean,'max_refined_Friedmann_residual_over_Hbg2':constraint,
        'max_final_patch_state_refinement_change':worst,
        'wave_background_subtracted_energy_drift_bound':wave_bounds,
        'noise_delay_cases':len(joint['noise']['two_pole_rows']),
        'new_empirical_likelihood':False,'new_native_tensor_simulation':False,
        'full_theory_closed':False}
    (HERE/'VALIDATION.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    def tex_sci(x):
        mant,ex=f'{x:.2e}'.split('e')
        return '$'+mant+r'\times10^{'+str(int(ex))+'}$'
    values=HERE/'Research note/values.tex'
    backup=HERE/'source_records/initial_values.tex'
    if not backup.exists():shutil.copyfile(values,backup)
    values.write_text('\\newcommand{\\MaxConstraintError}{'+tex_sci(constraint)+'}\n'
                     +'\\newcommand{\\MaxPatchDifference}{'+tex_sci(worst)+'}\n',encoding='utf-8')
    status=[
      {'connection':'Conservative stock dynamics','result':'Effective conservation framework assembled; equilibrium-selection obstruction identified.',
       'closed':'Energy/momentum exchange for the specified worldline action; conversion cancellation; controlled adiabatic scaling.',
       'open':'Physical redistribution/contact operator, common director dynamics, assembly and quantitative merger predictions.',
       'evidence':['results/stock_contact.json','results/connected_checks.json','formalization/ConnectedClosure.lean']},
      {'connection':'Response and carrier selection','result':'Passive-lag sign and a two-pole quantum noise-delay inequality established.',
       'closed':'Positive two-pole tracking comparison; F H mean_delay >= 4 for the stated response and temperature; stationary rate-rescaling freedom.',
       'open':'Initial occupation, carrier boundary, physical rates and spatial correlation volume. High-redshift tension remains.',
       'evidence':['results/connected_checks.json','figures/response_history.png','formalization/ConnectedClosure.lean']},
      {'connection':'Local release','result':'A new selected constitutive completion keeps positive energy/current and reproduces the tested linear cosmological branch.',
       'closed':'Action-level energy floor, regular-flow current positivity, timelike principal-speed bounds; exact original action for lambda>L(phi).',
       'open':'Selection of cubic and floor, global inhomogeneous well-posedness, nonlinear void statistics and multistream coupling.',
       'evidence':['results/adaptive_boundary_refined.json','results/local_waves.json','formalization/ConnectedClosure.lean']},
      {'connection':'Tensor sector','result':'Leading effective two-mode/luminal result connected to the chosen Einstein action and the existing TT algebra.',
       'closed':'TT-coordinate spanning and positivity; minimal-action principal symbol. This is conditional effective closure.',
       'open':'Native continuum, equilibrated tensor measurement, curvature/director/matter operator matching and full detector response.',
       'evidence':['results/connected_checks.json','formalization/ConnectedClosure.lean']},
      {'connection':'Matching and uniqueness','result':'Explicit deformations show which identities leave coefficients free.',
       'closed':'Loading reciprocity survives arbitrary positive loading; rate rescaling preserves equilibrium; background-preserving receiver family.',
       'open':'Physical loading and contact matrix elements; native G_R comparison; historical selection issue.',
       'evidence':['results/connected_checks.json','formalization/ConnectedClosure.lean']}
    ]
    (HERE/'closure_register.json').write_text(json.dumps(status,indent=2),encoding='utf-8')
    (HERE/'source_records/theorem_connections.json').write_text(json.dumps({
      'input_repository_head':manifest['github_head'],
      'existing_to_new':[
        {'existing':'Entropic/AppO/Release.lean:linear_positivity; Entropic/AppO/Flow.lean:release_positivity',
         'new':'current_factorization; rate_ratio_bounds; regular_rate_positivity',
         'meaning':'The selected constitutive completion removes the Q/current singularity for regular future-directed flow.'},
        {'existing':'Entropic/AppKN/Response.lean:two_pole_symbol; Entropic/Sweep/Analysis.lean:static_sum_rule',
         'new':'logarithmic_mean_bound; noise_delay_bound; two_pole_tracking',
         'meaning':'Connects the existing response to a delay/noise constraint and fixes the lag sign.'},
        {'existing':'Entropic/Reciprocity.lean:total_force_zero,comoving_exchange; Entropic/AppO/Release.lean:circular_jeans',
         'new':'relabeling_cancels; adiabatic_stock_scaling',
         'meaning':'Conservation and existence of an equilibrium do not select the physical RAR relaxation.'},
        {'existing':'Entropic/AppH10/Symbols.lean:tt_trace,tt_projector; Entropic/Pass2/Harmonic.lean:no_slip',
         'new':'tt_spans; tensor_energy_nonnegative; tensor_luminal_symbol; tensor_speed_deformation',
         'meaning':'Conditional Einstein tensor kinetics and an explicit operator freedom invisible to the static check.'},
        {'existing':'Entropic/Main/Galactic.lean:acceleration_abundance; Entropic/Main/Core.lean:abundance',
         'new':'loading_reciprocity; different_loading_changes_acceleration',
         'meaning':'The cross relation survives a loading change; physical selection of the loading remains separate.'}
      ]},indent=2),encoding='utf-8')
    css='''body{font:17px/1.55 system-ui,sans-serif;color:#172b38;background:#f6f8fa;margin:0}main{max-width:1080px;margin:0 auto;padding:42px 32px}h1{font-size:36px;line-height:1.15}h2{margin-top:36px;font-size:25px}a{color:#165ca0}table{border-collapse:collapse;width:100%;background:white;font-size:15px}td,th{padding:14px;border-bottom:1px solid #dbe2e8;text-align:left;vertical-align:top}th{background:#e9eff4}img{max-width:100%;background:white;border:1px solid #dbe2e8}code{font-size:90%}.box{background:white;border-left:5px solid #2f637a;padding:18px 22px}.small{font-size:14px;color:#425d6c}.links{display:flex;gap:20px;flex-wrap:wrap}.formula{font:21px/1.5 Georgia,serif;text-align:center;padding:15px;background:white}'''
    table=''.join('<tr><td><strong>'+html.escape(s['connection'])+'</strong></td><td>'+html.escape(s['result'])+'</td><td>'+html.escape(s['open'])+'</td></tr>' for s in status)
    page=f'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Connected theory closure</title><style>{css}</style><main>
<p class="small">SOL AND FABLE · RESEARCH CALCULATION · 23 OCTOBER 2026</p>
<h1>What closes, and what still needs a physical interaction</h1>
<p>A new effective construction addresses local exhaustion while preserving the tested linear cosmology. The other calculations establish useful restrictions and identify the physical choices that the existing proofs do not yet select.</p>
<p class="links"><a href="Research%20note/main.pdf"><strong>Read the derivation note (PDF)</strong></a><a href="closure_register.json">Closure register</a><a href="VALIDATION.json">Verification record</a><a href="REPRODUCE.txt">Reproduction guide</a></p>
<div class="box"><strong>All five questions were investigated; the full theory is not closed.</strong> The low-density completion is a specified effective hypothesis. Its equations and tests are concrete; its microscopic selection, nonlinear interfaces and multistream coupling remain open. The current papers and upstream Lean sources are preserved.</div>
<h2>A local release completion with an unchanged linear branch</h2>
<p>The new action adds pressure only when the auxiliary stock density falls below a threshold. Its minimum total energy is held constant. This makes the drain vanish as the future-directed current tends to zero, while preserving positive energy and subluminal local characteristics.</p>
<div class="formula">L(φ) = 3[K − V(φ)]<br>e(λ,φ) = λ/2 + 2[L(φ) − λ]<sub>+</sub><sup>3</sup> / [3L(φ)<sup>2</sup>]<br>λ ≥ L(φ)/2</div>
<p>For λ &gt; L the action is exactly the original constrained-clock action. On the saved cosmology, the threshold is at most <strong>{100*fine['max_cutoff_over_background_stock_through_today']:.3f}%</strong> of the homogeneous stock. Its background and linear perturbations therefore reproduce the archived fits at these parameters. This is an action identity, not a new fit or an acceptance test of nonlinear structure.</p>
<img src="figures/adaptive_boundary.png" alt="Positive auxiliary density and total energy in four homogeneous underdense patch tests">
<p class="small">These are homogeneous curved FRW patches with locally conserved radiation, not compensated void predictions. Maximum refined Friedmann residual: {constraint:.3g}; maximum final-state change on refinement: {worst:.3g}. The clock slows in the depleted phase.</p>
<p>The density-cutoff attempt that allowed clock reversal is retained in <a href="results/boundary_base.json">the earlier test record</a>. The final construction uses a constant total-energy floor, with a finite source rate at zero current.</p>
<h2>The five outcomes</h2><table><thead><tr><th>Connection</th><th>Result</th><th>Still open</th></tr></thead><tbody>{table}</tbody></table>
<h2>The remaining a₀ problem is dynamical</h2>
<p>At fixed baryonic acceleration, passive lag toward a declining equilibrium leaves an initially equilibrated response above that equilibrium. It cannot lower the predicted high-redshift force under those assumptions. A newly assembled, initially unoccupied response behaves differently and needs its own independently selected history.</p>
<img src="figures/response_history.png" alt="Passive response histories for equilibrated and initially unoccupied systems">
<p>The small cosmological mass loss also does too little in a controlled adiabatic halo calculation: from redshift 2.3 to today it gives an inferred acceleration-scale ratio of <strong>{stock['implied_a0_ratio_from_v4']:.3f}</strong>, compared with the required Hubble ratio <strong>{stock['required_H_tracking_a0_ratio']:.3f}</strong>. Relabeling committed stock as released stock leaves the total gravitational source unchanged. A redistribution mechanism is needed.</p>
<h2>Response speed and noise cannot be chosen independently</h2>
<div class="formula">𝓕 H τ̄ ≥ 4</div><p>This bound follows for the paper’s two-pole quantum response at horizon temperature. Rapid tracking requires a sufficiently large number of effectively independent cells to keep instantaneous force fluctuations small. Temporal averaging and spatial covariance must be included before comparison with observations.</p>
<h2>Proofs and tests</h2><p><strong>{lean['theorems']} standalone Lean certificates passed</strong>, with standard logical axioms only. The supplement uses the available Lean/mathlib 4.19 runtime; it does not rebuild the upstream 4.35 repository. <a href="formalization/ConnectedClosure.lean">Proof source</a> · <a href="source_records/theorem_connections.json">Connections to existing theorems</a></p>
<img src="figures/local_wave.png" alt="A one-dimensional pressure wave agrees with the predicted sound speed">
<p class="small">The regular wave frequency agrees with the analytic speed to 3.7 × 10⁻⁹ fractionally at the tested amplitude. Background-subtracted wave-energy drift is bounded by {max(wave_bounds):.2g}; the total-energy drift is smaller. No global PDE or interface-stability theorem is claimed.</p>
<h2>The physical input that would unlock the next step</h2><p>A specified interaction between the stock and its retained environment should determine the equilibrium target, relaxation rates, mechanical energy exchange, protected angular information and spatial noise. Detailed balance fixes rate ratios; it leaves their magnitude free. The existing static laws, positive maps and projector identities do not supply those matrix elements. The native geometric continuum is a separate unresolved task.</p>
<p class="small">Original input hashes verified: {len(manifest['inputs'])}. No current publication or upstream theorem file changed. Full derivations, assumptions and primary references are in the PDF.</p></main></html>'''
    (HERE/'START HERE.html').write_text(page,encoding='utf-8')
    print(json.dumps({'validation':report,'floor':fine['selected_energy_floor']}),flush=True)

if __name__=='__main__':main()
